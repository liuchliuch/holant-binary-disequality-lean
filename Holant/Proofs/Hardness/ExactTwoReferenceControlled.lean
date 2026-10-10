import Holant.Proofs.Hardness.ExactTwoReferenceCompiler
import Holant.Proofs.Hardness.ExactTwoReferenceSemantics
import Holant.Proofs.Hardness.ExactTwoChainPolynomial
import Holant.Proofs.Hardness.PairedPinsControlled
import Holant.Proofs.Reductions.ControlledCap

/-! Same-field computational global pinning.
The actual ring writer retains the original pin count as unary context. The
answer programme tests this count and multiplies by the fixed field element
1/2 precisely when the count is positive. Its semantic identity comes from
the full two-branch graph sum, and query/answer/storage bounds come from the
same physical preprocessor, arithmetic programme and context machine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceControlled
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler
namespace C
export ExactTwoReferenceCompiler (Input TargetInput sourceEncoding targetEncoding query queryComputes inputCountComputes)
end C
namespace R
export ExactTwoReferenceRaw (sourceArity targetArity raw count)
end R
namespace S
export ExactTwoReferenceSemantics (sourceSignatures targetSignatures exactTwo_factor)
end S
namespace P
export ExactTwoChainPolynomial (sourceValue sourceSignatures kernels)
end P
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap
  (controlledContextOfEq controlledContextOfEq_time controlledContextOfEq_machine controlledContext_atMostOne)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}
variable (F : FixedField K d)

abbrev sourceEncoding := C.sourceEncoding
abbrev targetEncoding := ExactTwoChainQueries.sourceEncoding

def sourceValue (r : C.Input) : K :=
  (r.val.realize r.property (S.sourceSignatures ExactTwoSignatures.q false)
    (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0

theorem target_signatures : S.targetSignatures (ExactTwoSignatures.q (K:=K))=P.sourceSignatures := by
  funext i
  fin_cases i <;> rfl

/-- The callee is exactly the literal q/E interpolation problem. -/
theorem query_value (r : C.Input) :
    P.sourceValue (C.query r)=(if R.count r.val=0 then 1 else 2)*sourceValue (K:=K) r := by
  have h := S.exactTwo_factor (K:=K) r.property
  rw [target_signatures] at h
  exact h

theorem source_value_eq_paired (r : C.Input) :
    sourceValue (K:=K) r=PairedPinsControlled.targetValue F
      (fun _ : Fin 1=>ExactTwoSignatures.q) (PairedPinsSemantics.pin false)
      (PairedPinsSemantics.pin true) (fun _ : Fin 1=>Signature.disequality) r := by
  simp only [PairedPinsControlled.targetValue,ExactSignatureTables.evaluate_eq_decoded,
    PairedPinsControlled.targetTables,LinearEquiv.apply_symm_apply]
  rfl

/-- The bound is calculated from these exact q/E tables in presentation F. -/
def targetTables : ExactSignatureTables d 2 1 ExactTwoChainQueries.arity where
  vertex i x := F.decode.symm (P.sourceSignatures i x)
  edge i a b := F.decode.symm (P.kernels i a b)

theorem target_value (r : C.TargetInput) : (targetTables F).evaluate F r=P.sourceValue r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

def targetOutput : PolynomialOutputBound targetEncoding F.encoding (P.sourceValue (K:=K)) := by
  simpa only [show (targetTables F).evaluate F=P.sourceValue from funext (target_value F)] using
    (targetTables F).outputBound F

abbrev contextEncoding := UnaryBinary.unaryEncoding
abbrev answerContextEncoding := pairEncoding F.encoding contextEncoding

def preprocess : Computes sourceEncoding (pairEncoding targetEncoding contextEncoding)
    (fun r=>(C.query r,R.count r.val)) :=
  pairComputes C.queryComputes C.inputCountComputes

def answerComputes : Computes (answerContextEncoding F) F.encoding (fun p : K×ℕ=>p.1) :=
  Wiring.firstComputes F.encoding contextEncoding

def countComputes : Computes (answerContextEncoding F) contextEncoding (fun p : K×ℕ=>p.2) :=
  Wiring.secondComputes F.encoding contextEncoding

def zeroComputes : Computes (answerContextEncoding F) encodingBoolBool
    (fun p : K×ℕ=>decide (p.2=0)) :=
  (pairComputes (countComputes F) (constantComputes (answerContextEncoding F) contextEncoding 0)).andThen
    (equalComputes contextEncoding)

def halfComputes : Computes (answerContextEncoding F) F.encoding (fun p : K×ℕ=>p.1*(2 : K)⁻¹) :=
  (pairComputes (answerComputes F)
    (constantComputes (answerContextEncoding F) F.encoding (2 : K)⁻¹)).andThen
    (Concrete.fieldMultiplication F)

def correction (p : K×ℕ) : K := if p.2=0 then p.1 else p.1*(2 : K)⁻¹

def correctionComputes : Computes (answerContextEncoding F) F.encoding correction :=
  congrComputes (ifComputes (zeroComputes F) (answerComputes F) (halfComputes F))
    (fun p=>by simp [correction])

theorem recovery (r : C.Input) : sourceValue (K:=K) r=
    correction (P.sourceValue (C.query r),R.count r.val) := by
  rw [query_value]
  unfold correction
  by_cases hm : R.count r.val=0
  · simp [hm]
  · simp only [hm,ite_false]
    have htwo : (2 : K)≠0 := by norm_num
    field_simp
    <;> ring

/-- No supplied safety, compiler, factor, nonzero denominator or successful
interpolation premise occurs in this one-query source. -/
def source : LengthControlledOracleReduction sourceEncoding F.encoding targetEncoding F.encoding
    (sourceValue (K:=K)) P.sourceValue :=
  Cap.controlledContextOfEq preprocess (correctionComputes F) (targetOutput F)
    sourceValue recovery

attribute [local irreducible] preprocess correctionComputes source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding P.sourceValue oracle) (r : C.Input) :=
  (source F).reduction.correct oracle ho r

def correction_outputs (p : K×ℕ) : TM2OutputsInTime (correctionComputes F).machine.computer
    ((answerContextEncoding F).encode p) (some (F.encoding.encode (correction p)))
    ((correctionComputes F).time.eval ((answerContextEncoding F).encode p).length) :=
  (correctionComputes F).outputs p

theorem correction_zero (a : K) : correction (a,0)=a := by simp [correction]
theorem correction_positive (a : K) (m : ℕ) (hm : 0<m) : correction (a,m)=a*(2 : K)⁻¹ := by
  simp [correction,Nat.ne_of_gt hm]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoReferenceControlled
