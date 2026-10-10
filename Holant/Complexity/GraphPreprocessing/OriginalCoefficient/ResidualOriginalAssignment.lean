import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPinSpec

/-! Original-coordinate assignment meaning of the derived residual descriptor.
This relates the emitted label to original incidences without any coefficient
value comparison or post hoc label selection. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- A selected pin affects exactly its original port occurrence. -/
theorem pinAt_selected (value : Bool) (r : RawClosedNetwork) (v : Fin r.vertices.length)
    (p : r.Ports arity) (j : Fin (arity (r.vertices.get v).1)) :
    ResidualLabel.pinAt (selected value r v p) j =
      if p = ⟨v,j⟩ then some value else none := by
  rcases p with ⟨u,i⟩
  by_cases hv : u=v
  · cases hv
    simp [selected,ResidualLabel.pinAt,eq_comm]
  · have hs : (⟨u,i⟩ : r.Ports arity) ≠ ⟨v,j⟩ := fun h => hv (congrArg Sigma.fst h)
    simp [selected,ResidualLabel.pinAt,hv,hs]

/-- Original executable inverse lookup is equivalent to testing the actual original route. -/
theorem pinAt_lookup (value : Bool) (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (q : Fin r.edges.length × Bool) (j : Fin (arity (r.vertices.get v).1)) :
    ResidualLabel.pinAt (selected value r v (r.lookup h q)) j =
      if r.route h ⟨v,j⟩ = q then some value else none := by
  rw [pinAt_selected]
  have he : r.lookup h q = ⟨v,j⟩ ↔ r.route h ⟨v,j⟩ = q := by
    constructor
    · intro hp; rw [← hp,r.route_lookup]
    · intro hp
      apply (r.route_bijective h).1
      rw [r.route_lookup,hp]
  simp only [he]

/-- The deleted edge's own original end chooses its independently supplied bit;
every original port on another edge receives zero. -/
def originalAssignment (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (e : Fin r.edges.length) (v : Fin r.vertices.length) (a z : Bool)
    (j : Fin (arity (r.vertices.get v).1)) : Bool :=
  if (r.route h ⟨v,j⟩).1=e then if (r.route h ⟨v,j⟩).2 then z else a else false

/-- Exact ordered original assignment equality, including loops and nonincident vertices. -/
theorem zeroDescriptor_assignment (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (e : Fin r.edges.length) (v : Fin r.vertices.length) (a z : Bool) :
    ResidualLabel.assignment (zeroDescriptor r h e v a z) = originalAssignment r h e v a z := by
  funext j
  unfold ResidualLabel.assignment zeroDescriptor
  dsimp only
  rw [pinAt_lookup,pinAt_lookup]
  unfold originalAssignment
  generalize hq : r.route h ⟨v,j⟩ = q
  rcases q with ⟨f,side⟩
  cases side <;> by_cases hf : f=e <;> simp [hf]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualPin
