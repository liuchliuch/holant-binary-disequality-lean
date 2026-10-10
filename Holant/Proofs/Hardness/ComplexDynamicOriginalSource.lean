import Holant.Proofs.Hardness.ComplexDynamicOriginalData
import Holant.Proofs.Hardness.ComplexDynamicSource

/-! Exact original-M factory for the complex norm-cone self-dual branch.
The original algebraic coefficients supply the field, fixed stage multiplier,
canonical complex inclusion and unchanged answer presentation. All programmes are internal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicOriginalSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export ComplexDynamicOriginalData (Applicable alpha beta gamma alpha_nonzero beta_nonzero gamma_nonzero
  parameters alpha_value beta_value gamma_value target_value)
end D
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
set_option backward.isDefEq.respectTransparency false
variable (M : Signature ℂ 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (h : D.Applicable M)
local instance fieldAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'

def source : LengthControlledOracleReduction SparseUnitValue.encoding (O.presentation M halg).encoding
    O.targetEncoding (O.presentation M halg).encoding
    (SparseUnitValue.value (K:=O.field M)) (O.targetValue M halg) := by
  have r := ComplexDynamicSource.source (O.presentation M halg) (D.alpha M) (D.beta M) (D.gamma M)
    (D.alpha_nonzero M h) (D.beta_nonzero M h) (D.gamma_nonzero M h)
    (D.parameters M h) (O.field M).subtype
    (D.alpha_value M h) (D.beta_value M h) (D.gamma_value M h)
  have he : ThreeModeGraphEvaluation.targetValue (D.alpha M) (D.beta M) (D.gamma M)=
      O.targetValue M halg := funext (D.target_value M halg h)
  rw [he] at r
  exact r

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (r : SparseUnitValue.Input) := (source M halg h).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicOriginalSource
