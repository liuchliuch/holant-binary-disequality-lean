import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonAssignment
import Holant.OneHot.Computable.Evaluation.Conditioning

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonCoefficient
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option Elab.async false

theorem literal_eq_original (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    literal a z x = some (.inl ⟨x.val.1.val.signatureLabel x.val.1.property x.val.2.1,
      ResidualSingleton.originalAssignment a z x⟩) := by
  change (some (Sum.inl ⟨x.val.1.val.signatureLabel x.val.1.property x.val.2.1,
    ResidualLabel.assignment (ResidualSingleton.descriptor a z x)⟩) : RawClosedNetwork.TreeLabel s b arity) = _
  rw [ResidualSingleton.descriptor_assignment]

/-- The residual assignment singles out the actual original surviving endpoint.
Its increasing local enumeration is the executable conditioned graph's own. -/
def survivingWord (x : Input (s := s) (b := b) (arity := arity)) :
    Fin (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPorts x.val.2.2.1 x.val.2.1).card → Bool :=
  fun i => decide (x.val.1.val.route x.val.1.property ⟨x.val.2.1,
    (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPortEquiv
      x.val.2.2.1 x.val.2.1 i).val⟩ = x.val.2.2.2)

/-- On an incident surviving endpoint this is a single selected remaining
port, never a replacement local coordinate chosen by semantic equality. -/
theorem survivingWord_at (x : Input (s := s) (b := b) (arity := arity))
    (j : Fin (arity (x.val.1.val.vertices.get x.val.2.1).1))
    (hj : ResidualSurvivorQuery.selected (ResidualSingleton.survivorQuery x) = some j)
    (i : Fin (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPorts x.val.2.2.1 x.val.2.1).card) :
    survivingWord x i = decide ((((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPortEquiv
      x.val.2.2.1 x.val.2.1 i).val = j) := by
  have hr := (ResidualSingleton.survivor_eq_some x j).mp hj
  unfold survivingWord
  apply decide_eq_decide.mpr
  rw [← hr]
  constructor
  · intro h
    have he := (x.val.1.val.route_bijective x.val.1.property).1 h
    exact Fin.ext (congrArg (fun p : x.val.1.val.Ports arity => p.2.val) he)
  · intro h
    rw [h]

/-- Literal original coefficient label equality with the executable conditioned
network. No field values, equality search or chosen replacement labels occur. -/
theorem literal_eq_conditioned (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    literal a z x =
      (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableConditionEdge x.val.2.2.1 a z).vertex
        x.val.2.1 (survivingWord x) := by
  rw [literal_eq_original]
  apply congrArg (fun f : Fin (arity (x.val.1.val.vertices.get x.val.2.1).1) → Bool =>
    (some (Sum.inl ⟨x.val.1.val.signatureLabel x.val.1.property x.val.2.1,f⟩) : RawClosedNetwork.TreeLabel s b arity))
  funext j
  change ResidualSingleton.originalAssignment a z x j =
    if h : (x.val.1.val.route x.val.1.property ⟨x.val.2.1,j⟩).1=x.val.2.2.1 then
      (if (x.val.1.val.route x.val.1.property ⟨x.val.2.1,j⟩).2 then z else a)
    else survivingWord x ((((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPortEquiv
      x.val.2.2.1 x.val.2.1).symm ⟨j,h⟩)
  unfold ResidualSingleton.originalAssignment
  split <;> simp_all [survivingWord]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonCoefficient
