import Holant.Proofs.Hardness.ComplexDynamicInterpolation
import Holant.Proofs.Hardness.SelfDualReferenceControlled
import Holant.Proofs.Hardness.DenseEOUnitCompiler
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! Closed native ONE/TWO producer for the complex norm-cone self-dual
branch. Dense unit macros, coherent reference ring, actual dynamic queries and
field arithmetic compose in one unchanged coefficient-field presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicSource
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
export ComplexDynamicInterpolation (source)
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
variable (params : ComplexDynamicParameters.Data) (σ : K→+*ℂ)
variable (haComplex : σ a=params.a) (hbComplex : σ b=params.b) (hcComplex : σ c=params.c)

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
    (I.source a b c F params σ haComplex hbComplex hcComplex)

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle ExactTwoChainQueries.targetEncoding F.encoding (G.targetValue a b c) oracle)
    (r : SparseUnitValue.Input) :=
  (source F a b c ha hb hc params σ haComplex hbComplex hcComplex).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicSource
