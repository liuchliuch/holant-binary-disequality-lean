import Holant.Proofs.Hardness.ExactTwoReferenceObservations

/-! Universal weighted self-dual computational pinning.
For every actual self-dual quaternary q, the same physical single-cycle writer
and count-sensitive half decoder reduce [q,01] to [q,E], in one fixed field.
No support, nonzero-coefficient, local pin realization or interpolation success
is assumed. This does not assert E access from arbitrary weighted q. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SelfDualReferenceControlled
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
namespace U
export ExactTwoReferenceControlled
  (sourceEncoding targetEncoding preprocess correction correctionComputes recovery source_machine)
end U
namespace C
export ExactTwoReferenceCompiler (Input TargetInput query)
end C
namespace R
export ExactTwoReferenceRaw (count)
end R
namespace S
export ExactTwoReferenceSemantics (sourceSignatures targetSignatures denote_factor)
end S
namespace SD
export SelfDualPinObstruction (SelfDual)
end SD
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap
  (controlledContextOfEq controlledContextOfEq_time controlledContextOfEq_machine)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d : ℕ}
variable (F : FixedField K d) (q : Signature K 4)

abbrev sourceEncoding := U.sourceEncoding
abbrev targetEncoding := U.targetEncoding

def sourceValue (r : C.Input) : K :=
  (r.val.realize r.property (S.sourceSignatures q false)
    (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0

def targetValue (r : C.TargetInput) : K :=
  (r.val.realize r.property (S.targetSignatures q)
    (fun _ : Fin 1=>Signature.disequality)).denote Fin.elim0

def targetTables : ExactSignatureTables d 2 1 ExactTwoChainQueries.arity where
  vertex i x := F.decode.symm (S.targetSignatures q i x)
  edge _ a b := F.decode.symm (Signature.disequality a b)

theorem target_evaluate (r : C.TargetInput) : (targetTables F q).evaluate F r=targetValue q r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

def targetOutput : PolynomialOutputBound targetEncoding F.encoding (targetValue q) := by
  simpa only [show (targetTables F q).evaluate F=targetValue q from funext (target_evaluate F q)] using
    (targetTables F q).outputBound F

theorem source_value_eq_paired (r : C.Input) :
    sourceValue q r=PairedPinsControlled.targetValue F
      (fun _ : Fin 1=>q) (PairedPinsSemantics.pin false)
      (PairedPinsSemantics.pin true) (fun _ : Fin 1=>Signature.disequality) r := by
  simp only [PairedPinsControlled.targetValue,ExactSignatureTables.evaluate_eq_decoded,
    PairedPinsControlled.targetTables,LinearEquiv.apply_symm_apply]
  rfl

variable (hq : SD.SelfDual q)
include hq in
theorem query_value (r : C.Input) :
    targetValue q (C.query r)=(if R.count r.val=0 then 1 else 2)*sourceValue q r :=
  S.denote_factor r.property q hq

include hq in
theorem recovery (r : C.Input) : sourceValue q r=
    U.correction (targetValue q (C.query r),R.count r.val) := by
  rw [query_value q hq]
  unfold U.correction
  by_cases hm : R.count r.val=0
  · simp [hm]
  · simp only [hm,ite_false]
    have htwo : (2 : K)≠0 := by norm_num
    field_simp
    <;> ring

/-- The caller supplies the mathematical bit-flip symmetry of q, not a
realization, value equation for the transformed graph or desired reduction. -/
def source : LengthControlledOracleReduction sourceEncoding F.encoding targetEncoding F.encoding
    (sourceValue q) (targetValue q) :=
  Cap.controlledContextOfEq U.preprocess (U.correctionComputes F) (targetOutput F q)
    (sourceValue q) (recovery q hq)

attribute [local irreducible] U.preprocess U.correctionComputes

/-- The weighted generalization has literally the same finite programme. -/
theorem source_machine : (source F q hq).reduction.machine=
    (ExactTwoReferenceControlled.source F).reduction.machine := by
  rw [U.source_machine]
  unfold source
  exact Cap.controlledContextOfEq_machine _ _ _ _ _

theorem source_clock : (source F q hq).reduction.time=
    (OracleOneQuery.Context.reduction U.preprocess (U.correctionComputes F) (targetOutput F q)).time := by
  unfold source
  exact Cap.controlledContextOfEq_time _ _ _ _ _

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle targetEncoding F.encoding (targetValue q) oracle) (r : C.Input) :=
  (source F q hq).reduction.correct oracle ho r

theorem atMostOne : UniversalPairReduction.ThreeQuery.AtMostQueries (source F q hq).reduction.machine 1 := by
  rw [source_machine]
  exact ExactTwoReferenceControlled.atMostOne F

theorem exactTwo_sourceValue (r : C.Input) :
    sourceValue (ExactTwoSignatures.q (K:=K)) r=ExactTwoReferenceControlled.sourceValue r := rfl

theorem exactTwo_targetValue (r : C.TargetInput) :
    targetValue (ExactTwoSignatures.q (K:=K)) r=ExactTwoChainPolynomial.sourceValue r := by
  unfold targetValue
  rw [ExactTwoReferenceControlled.target_signatures]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SelfDualReferenceControlled
