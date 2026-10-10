import Holant.OpenNetwork
import Holant.TwoPorts

/-! Isolated structural edge boxes represented in the full half-edge model. -/

namespace Holant
namespace OpenNetworkShape

def edgeBox : OpenNetworkShape 2 where
  vertices := 0
  arity := Fin.elim0
  free := 2
  edges := 1
  boundary := ⟨Sum.inr, Sum.inr_injective⟩
  ends := {
    toFun := fun q => .inr (finTwoEquiv.symm q.2)
    inj' := by
      intro a b h
      apply Prod.ext (Subsingleton.elim _ _)
      exact finTwoEquiv.symm.injective (Sum.inr.inj h) }
  ordinary_boundary_iff_unpaired := fun p => Fin.elim0 p.1
  freeBoundary := id
  free_boundary := fun _ => rfl
  freeEdge := fun f => (0, finTwoEquiv f)
  free_paired := fun f => congrArg Sum.inr (finTwoEquiv.symm_apply_apply f)

end OpenNetworkShape

namespace OpenNetwork

variable {K : Type*} [CommSemiring K]

/-- The edge box has no signature vertices and exactly one structural wire. -/
def edgeBox (W : EdgeKind) : OpenNetwork K 2 where
  shape := OpenNetworkShape.edgeBox
  vertex := fun v => Fin.elim0 v
  edge := fun _ => W

private def edgeBoxAssignment (x : Fin 2 → Bool) :
    OpenPorts 0 Fin.elim0 2 → Bool := Sum.elim (fun p => Fin.elim0 p.1) x

private theorem edgeBox_assignment_unique (x : Fin 2 → Bool)
    (z : OpenPorts 0 Fin.elim0 2 → Bool) :
    (∀ j, z (.inr j) = x j) ↔ z = edgeBoxAssignment x := by
  constructor
  · intro h
    funext p
    cases p with
    | inl q => exact Fin.elim0 q.1
    | inr j => exact h j
  · rintro rfl
    intro j
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem raw_edgeBox (W : EdgeKind) (x : Fin 2 → Bool) :
    (edgeBox (K := K) W).raw x = W.value (x 0) (x 1) := by
  unfold raw
  dsimp [edgeBox, OpenNetworkShape.edgeBox]
  simp only [edgeBox_assignment_unique]
  simp [weight, edgeBoxAssignment, finTwoEquiv]

theorem boundaryKernel_edgeBox (W : EdgeKind) (j : Fin 2) :
    (edgeBox (K := K) W).boundaryKernel j = W.value := rfl

/-- The boundary-corrected tensor of an isolated I/X edge box is its kernel once. -/
theorem tensor_edgeBox (W : EdgeKind) (x : Fin 2 → Bool) :
    (edgeBox (K := K) W).tensor x = W.value (x 0) (x 1) := by
  rw [tensor, Signature.coordinateAction_two]
  simp only [boundaryKernel_edgeBox, raw_edgeBox, Fin.cons_zero, Fin.cons_one]
  cases W <;> cases hx : x 0 <;> cases hy : x 1 <;>
    simp [EdgeKind.value, Signature.equality, Signature.disequality]

/-- Closing the native primitive by a native contraction preserves its scalar 2. -/
theorem close_native_edgeBox (x : Fin 0 → Bool) :
    Signature.contract Signature.disequality
      (edgeBox (K := K) .disequality).tensor x = 2 := by
  simp [Signature.contract_disequality, tensor_edgeBox, EdgeKind.value,
    Signature.disequality, one_add_one_eq_two]

end OpenNetwork
end Holant
