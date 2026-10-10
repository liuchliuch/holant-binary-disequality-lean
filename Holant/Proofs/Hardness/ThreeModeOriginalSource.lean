import Holant.Proofs.Hardness.ThreeModeOriginalData
import Holant.Proofs.Hardness.ThreeModeSource

/-! Exact original-M factory for the stated norm-dominant self-dual EO subcase.
The original algebraic entries generate the field and answer presentation.
No backend, embedding, infinite-order proof, or desired hardness is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeOriginalSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export ThreeModeOriginalData (Applicable alpha beta gamma alpha_nonzero beta_nonzero gamma_nonzero
  field_dominantPlus field_dominantMinus target_value)
end D
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [NormedField L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : D.Applicable M)
local instance fieldAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'

def source : LengthControlledOracleReduction SparseUnitValue.encoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding
    (SparseUnitValue.value (K:=O.field M)) (O.targetValue M halg) := by
  have r := ThreeModeSource.source (O.presentation M halg) (D.alpha M) (D.beta M) (D.gamma M)
    (D.alpha_nonzero M h) (D.beta_nonzero M h) (D.gamma_nonzero M h)
    (D.field_dominantPlus M h) (D.field_dominantMinus M h)
  have he : ThreeModeGraphEvaluation.targetValue (D.alpha M) (D.beta M) (D.gamma M)=
      O.targetValue M halg := funext (D.target_value M halg h)
  rw [he] at r
  exact r

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (r : SparseUnitValue.Input) := (source M halg h).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeOriginalSource
