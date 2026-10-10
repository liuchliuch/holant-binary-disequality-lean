import Holant.TensorClosure
import Holant.BoundaryAction

/-! Actual coordinate actions distribute through finite disjoint tensor factors. -/

namespace Holant.TensorDecomposition

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Assignments transported through the recorded ordered port partition. -/
def assignments (D : TensorDecomposition K n) :
    (Fin n → Bool) ≃ ((i : Fin D.count) → Fin (D.arity i) → Bool) :=
  (Equiv.arrowCongr D.ports.symm (Equiv.refl Bool)).trans
    (Equiv.piCurry (fun i (_ : Fin (D.arity i)) => Bool))

@[simp] theorem assignments_apply (D : TensorDecomposition K n) (x : Fin n → Bool)
    (i : Fin D.count) (j : Fin (D.arity i)) :
    D.assignments x i j = x (D.ports ⟨i, j⟩) := rfl

theorem prod_ports (D : TensorDecomposition K n) (f : Fin n → K) :
    (∏ i, ∏ j, f (D.ports ⟨i, j⟩)) = ∏ k, f k := by
  rw [← Fintype.prod_sigma (fun p => f (D.ports p))]
  exact D.ports.prod_comp f

/-- Apply the same binary matrix to every factor slot, retaining the actual scalar. -/
def mapAction (D : TensorDecomposition K n) (M : Kernel K) : TensorDecomposition K n where
  count := D.count
  arity := D.arity
  factor := fun i => Signature.coordinateAction (fun _ => M) (D.factor i)
  ports := D.ports
  scale := D.scale

set_option backward.isDefEq.respectTransparency false in
/-- Finite Fubini gives a factorization of the transformed tensor, not merely an
invariance claim about its rank or support. -/
theorem value_mapAction (D : TensorDecomposition K n) (M : Kernel K) :
    (D.mapAction M).value = Signature.coordinateAction (fun _ => M) D.value := by
  funext x
  simp only [value, mapAction, Signature.coordinateAction]
  rw [Fintype.prod_sum, Finset.mul_sum]
  symm
  apply Fintype.sum_equiv D.assignments
  intro y
  change (∏ k, M (x k) (y k)) *
      ((D.scale : K) * ∏ i, D.factor i (fun j => y (D.ports ⟨i, j⟩))) =
    (D.scale : K) * ∏ i,
      ((∏ j, M (x (D.ports ⟨i, j⟩)) (y (D.ports ⟨i, j⟩))) *
        D.factor i (fun j => y (D.ports ⟨i, j⟩)))
  rw [Finset.prod_mul_distrib, D.prod_ports (fun k => M (x k) (y k))]
  ac_rfl

end Holant.TensorDecomposition

namespace Holant.Signature

variable {K : Type*} [Field K] {n : ℕ}

/-- A pointwise class transformation lifts to the class's true tensor closure. -/
theorem TensorClosure.map_action
    {C D : (m : ℕ) → Signature K m → Prop} {f : Signature K n}
    (M : Kernel K) (hmap : ∀ m g, C m g → D m (coordinateAction (fun _ => M) g))
    (hf : TensorClosure C f) : TensorClosure D (coordinateAction (fun _ => M) f) := by
  obtain ⟨T, hT, rfl⟩ := hf
  exact ⟨T.mapAction M, fun i => hmap _ _ (hT i), T.value_mapAction M⟩

end Holant.Signature
