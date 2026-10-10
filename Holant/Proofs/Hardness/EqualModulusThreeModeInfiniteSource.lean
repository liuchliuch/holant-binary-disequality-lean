import Holant.Proofs.Hardness.EqualModulusThreeModeInterpolation
import Holant.Proofs.Hardness.SelfDualReferenceControlled
import Holant.Proofs.Hardness.DenseEOUnitCompiler
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! Internal same-field composition for the nonresonant branch of the finite
equal-modulus test. The actual dense source, coherent reference, and full
three-mode annihilator are composed without any new oracle signature. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeInfiniteSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace S
export ThreeModeSignatures (original eo middle self_dual)
end S
namespace Ref
export SelfDualReferenceControlled (source sourceValue targetValue source_value_eq_paired)
end Ref
namespace G
export ThreeModeGraphEvaluation (sourceValue targetValue sourceSignatures)
end G
namespace I
export EqualModulusThreeModeInterpolation (source)
end I
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K)
local instance fieldCharZero : CharZero K := algebraRat.charZero K

omit [Algebra ℚ K] in
theorem reference_value (r : ExactTwoChainQueries.Input) :
    Ref.targetValue (S.original a b c) r=G.sourceValue a b c r := by
  have h : ExactTwoReferenceSemantics.targetSignatures (S.original a b c)=
      G.sourceSignatures a b c := by
    funext i
    fin_cases i <;> rfl
  unfold Ref.targetValue G.sourceValue
  rw [h]
  rfl

variable (ha : a≠0) (hb : b≠0) (hc : c≠0)
variable (hd : ∀m : ℕ, ThreeModeAnnihilator.denominator m c (a+b) (b-a)≠0)

/-- Same-field controlled source, with only explicit original scalar premises. -/
def source : LengthControlledOracleReduction SparseUnitValue.encoding F.encoding
    ExactTwoChainQueries.targetEncoding F.encoding
    (SparseUnitValue.value (K:=K)) (G.targetValue a b c) := by
  let first := DenseEOUnitCompiler.controlled F (S.original a b c)
    (S.eo a b c) (S.middle a b c ha hb hc)
  have hfirst : DenseEOUnitCompiler.targetValue F (S.original a b c)=
      Ref.sourceValue (S.original a b c) := by
    funext r
    exact (Ref.source_value_eq_paired F (S.original a b c) r).symm
  rw [hfirst] at first
  let reference := Ref.source F (S.original a b c) (S.self_dual a b c)
  have href : Ref.targetValue (S.original a b c)=G.sourceValue a b c :=
    funext (reference_value a b c)
  rw [href] at reference
  exact Compose.composeControlled (Compose.composeControlled first reference)
    (I.source a b c F hd)

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle ExactTwoChainQueries.targetEncoding F.encoding (G.targetValue a b c) oracle)
    (r : SparseUnitValue.Input) :=
  (source F a b c ha hb hc hd).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeInfiniteSource
