import Holant.Proofs.Hardness.EqualModulusThreeModeOriginalData

/-! Closed original-complex-signature source for either equal-modulus
spectral arm with the other mode strictly smaller. The finite exponent is
computed from the original generated field, and all oracle bytes use it. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeOriginalSource
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export EqualModulusThreeModeOriginalData (Applicable alpha beta gamma field_spectral
  alpha_nonzero beta_nonzero gamma_nonzero target_value)
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
  let := FiniteCapLocal.original_finiteDimensional M halg
  have r := EqualModulusThreeModeSource.source (O.presentation M halg)
    (O.field M).subtype (D.alpha M) (D.beta M) (D.gamma M)
    (D.alpha_nonzero M h) (D.beta_nonzero M h) (D.gamma_nonzero M h) (D.field_spectral M h)
  have he : ThreeModeGraphEvaluation.targetValue (D.alpha M) (D.beta M) (D.gamma M)=
      O.targetValue M halg := funext (D.target_value M halg h)
  rw [he] at r
  exact r

attribute [local irreducible] source

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding (O.presentation M halg).encoding (O.targetValue M halg) oracle)
    (r : SparseUnitValue.Input) :
    (source M halg h).reduction.machine.OutputsInTime oracle (SparseUnitValue.encoding.encode r)
      ((O.presentation M halg).encoding.encode (SparseUnitValue.value r))
      ((source M halg h).reduction.time.eval (SparseUnitValue.encoding.encode r).length) :=
  (source M halg h).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EqualModulusThreeModeOriginalSource
