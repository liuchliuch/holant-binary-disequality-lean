import Holant.Proofs.Hardness.TwoCoefficientStageAccess
import Holant.Proofs.Hardness.TwoCoefficientRatioEscape
import Holant.Proofs.Hardness.TwoCoefficientInterpolation
import Holant.Proofs.Hardness.SelfDualReferenceControlled
import Holant.Proofs.Hardness.DenseEOUnitCompiler

/-! Full pin-free hard-basis source for two nonzero EO coefficients.
The original finite presentation is fixed throughout. An internally derived
complex embedding selects depth0/1/2, hence an actual original-q template of
at most four vertices. Every normalization denominator and selected coefficient
is proved nonzero. No spectral, gadget, reduction or hardness premise is input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientSource
open Computability Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace E
export TwoCoefficientRatioEscape (depth selected selected_nonzero selected_infinite depth_le_two)
end E
namespace S
export TwoCoefficientSignatures (weighted eo middle self_dual)
end S
namespace Ref
export SelfDualReferenceControlled (source sourceValue targetValue source_value_eq_paired)
end Ref
namespace I
export TwoCoefficientInterpolation (source sourceValue targetValue literalSignatures)
end I
namespace A
export TwoCoefficientStageAccess (source value)
end A
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b : K)
local instance fieldCharZero : CharZero K := algebraRat.charZero K

theorem reference_value (r : ExactTwoChainQueries.Input) :
    Ref.targetValue (S.weighted a b) r=I.sourceValue a b r := by
  have h : ExactTwoReferenceSemantics.targetSignatures (S.weighted a b)=I.literalSignatures a b := by
    funext i
    fin_cases i <;> rfl
  unfold Ref.targetValue I.sourceValue
  rw [h]
  rfl

theorem interpolation_value (r : ExactTwoChainQueries.TargetInput) :
    I.targetValue a b r=A.value a b r := rfl

variable (ha : a≠0) (hb : b≠0)

/-- Internally selected coefficients; the endpoint is the original aE+bB. -/
def source : LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
    ExactTwoChainQueries.targetEncoding F.encoding
    (SparseUnitValue.value (K:=K)) (A.value a b) := by
  let p := E.selected F a b
  have hp := E.selected_nonzero F a b ha hb
  let first := DenseEOUnitCompiler.controlled F (S.weighted p.1 p.2)
    (S.eo p.1 p.2) (S.middle p.1 p.2 hp.1 hp.2)
  have hfirst : DenseEOUnitCompiler.targetValue F (S.weighted p.1 p.2)=
      Ref.sourceValue (S.weighted p.1 p.2) := by
    funext r
    exact (Ref.source_value_eq_paired F (S.weighted p.1 p.2) r).symm
  rw [hfirst] at first
  let ring := Ref.source F (S.weighted p.1 p.2) (S.self_dual p.1 p.2)
  have hring : Ref.targetValue (S.weighted p.1 p.2)=I.sourceValue p.1 p.2 :=
    funext (reference_value p.1 p.2)
  rw [hring] at ring
  let interp := I.source p.1 p.2 hp.1 hp.2 (E.selected_infinite F a b ha hb) F
  have hinterp : I.targetValue p.1 p.2=A.value p.1 p.2 :=
    funext (interpolation_value p.1 p.2)
  rw [hinterp] at interp
  exact Compose.composeControlled (Compose.composeControlled (Compose.composeControlled first ring) interp)
    (A.source F a b (E.depth F a b).val)

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle ExactTwoChainQueries.targetEncoding F.encoding (A.value a b) oracle)
    (r : SparseUnitValue.Input) :
    (source F a b ha hb).reduction.machine.OutputsInTime oracle (SparseUnitValue.encoding.encode r)
      (F.encoding.encode (SparseUnitValue.value r))
      ((source F a b ha hb).reduction.time.eval (SparseUnitValue.encoding.encode r).length) :=
  (source F a b ha hb).reduction.correct oracle ho r

/-- The finite escape really selects an at-most-four-original-vertex macro. -/
theorem selected_template_bound :
    (TwoCoefficientStageAccess.template a b (E.depth F a b).val).vertices.length≤4 ∧
    (TwoCoefficientStageAccess.template a b (E.depth F a b).val).edges.length≤6 := by
  simpa only [TwoCoefficientStageAccess.template,Labelling.template,List.length_ofFn] using
    TwoCoefficientStage.bounded_counts a b (E.depth F a b).val (E.depth_le_two F a b)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.TwoCoefficientSource
