import Holant.Proofs.Hardness.PositiveBoundaryInterpolation
import Holant.Proofs.Hardness.TwoCoefficientSource

/-! The positive triangle-equality boundary reduces conventional hard native
ONE/TWO graphs to the ORIGINAL q oracle, in any fixed presentation F. The hard
row H is obtained from the accepted two-coefficient producer and physically
included as label1 of [q,H], then removed by actual positive q chains. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveBoundarySource
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity Input TargetInput sourceEncoding targetEncoding)
end Q
namespace I
export PositiveBoundaryInterpolation (source sourceValue targetValue literalSignatures kernels)
end I
namespace A
export TwoCoefficientStageAccess (value signatures)
end A
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K)
local instance fieldCharZero : CharZero K := algebraRat.charZero K

/-- Literal inclusion of H-only source rows into the marked H dictionary slot. -/
def templates (_ : ℕ) : Template := identityTemplate Q.arity 1

theorem hypotheses : ∀i<1,
    (templates i).WellFormed 2 1 Q.arity ∧ (templates i).boundary=Q.arity i :=
  fun _ _=>⟨identityTemplate_wellFormed Q.arity (1 : Fin 2),rfl⟩

def query : Q.TargetInput → Q.Input :=
  Compiler.value 1 1 Q.arity templates 2 Q.arity hypotheses

def queryComputes : Computes Q.targetEncoding Q.sourceEncoding query :=
  Compiler.computes 1 1 Q.arity templates 2 Q.arity hypotheses

theorem query_value (r : Q.TargetInput) :
    I.sourceValue a b c (query r)=A.value (1 : K) (1/2) r := by
  have hp := replacement_partition templates r.val r.property
    (fun i hi=>(hypotheses i hi).1)
    (A.signatures (1 : K) (1/2)) (I.literalSignatures a b c) I.kernels
    (fun _ : Fin 1=>(1 : K)) (fun i=>by
      simpa only [templates,one_smul,I.literalSignatures,A.signatures,PositiveBoundarySignatures.H,
        Fin.val_one,ite_true] using
        identityTemplate_denote Q.arity (1 : Fin 2) (I.literalSignatures a b c) (I.kernels (K:=K)))
  simp only [Finset.prod_const_one,one_mul] at hp
  exact hp

def literalTables : ExactSignatureTables d 2 1 Q.arity where
  vertex i x := F.decode.symm (I.literalSignatures a b c i x)
  edge i x y := F.decode.symm (I.kernels i x y)

theorem literal_evaluate (r : Q.Input) :
    (literalTables F a b c).evaluate F r=I.sourceValue a b c r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,literalTables,LinearEquiv.apply_symm_apply]
  rfl

def literalOutput : PolynomialOutputBound Q.sourceEncoding F.encoding (I.sourceValue a b c) where
  bound := ((literalTables F a b c).outputBound F).bound
  length_le r := by
    rw [←literal_evaluate F a b c r]
    exact ((literalTables F a b c).outputBound F).length_le r

/-- An actual one-query row compiler with the unchanged F answer copier. -/
def inclusion : LengthControlledOracleReduction Q.targetEncoding F.encoding
    Q.sourceEncoding F.encoding (A.value (1 : K) (1/2)) (I.sourceValue a b c) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq queryComputes
    (identityComputes F.encoding) (literalOutput F a b c)
    (A.value (1 : K) (1/2)) (fun r=>(query_value a b c r).symm)

variable [LinearOrder K] [IsStrictOrderedRing K]
variable (ha : 0<a) (hb : 0<b) (hc : c=a+b) (hnu : b-a≠0)

/-- No free H gadget, evaluator, spectral certificate, termination or hardness
premise is input. All query and arithmetic programmes come from actual sources. -/
def source : LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
    Q.targetEncoding F.encoding (SparseUnitValue.value (K:=K)) (I.targetValue a b c) :=
  Compose.composeControlled
    (Compose.composeControlled
      (TwoCoefficientSource.source F (1 : K) (1/2) (by norm_num) (by norm_num))
      (inclusion F a b c))
    (I.source a b c hc (ne_of_gt (by rw [hc]; exact add_pos ha hb)) hnu
      (PositiveBoundarySignatures.infinite_ratio a b c ha hb hc hnu) F)

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (I.targetValue a b c) oracle)
    (r : SparseUnitValue.Input) :=
  (source F a b c ha hb hc hnu).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveBoundarySource
