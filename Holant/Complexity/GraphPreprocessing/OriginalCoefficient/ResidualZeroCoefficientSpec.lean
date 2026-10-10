import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalAssignment
import Holant.OneHot.Computable.Evaluation.Conditioning

/-! Exact original table-entry meaning of the physically emitted coefficient.
The label is obtained directly from original incidences and stored signature ID. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- No coefficient-value equality or later label choice enters this identity. -/
theorem literal_eq_original (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    literal a z x = some (.inl ⟨x.1.val.signatureLabel x.1.property x.2.1,
      ResidualPin.originalAssignment x.1.val x.1.property x.2.2 x.2.1 a z⟩) := by
  change (some (Sum.inl ⟨x.1.val.signatureLabel x.1.property x.2.1,
    ResidualLabel.assignment (ResidualPin.zeroDescriptor x.1.val x.1.property x.2.2 x.2.1 a z)⟩) :
      RawClosedNetwork.TreeLabel s b arity) = _
  rw [ResidualPin.zeroDescriptor_assignment]

/-- The actual emitted label is the executable conditioned network's zero coefficient. -/
theorem literal_eq_conditioned_zero (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    literal a z x =
      (((x.1.val.labelNetwork x.1.property).asFinite).executableConditionEdge x.2.2 a z).vertex x.2.1 (fun _ => false) := by
  rw [literal_eq_original]
  rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficient
