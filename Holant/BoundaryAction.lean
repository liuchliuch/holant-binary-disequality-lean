import Holant.Kernel
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Ordered coordinatewise action on a Boolean tensor, using ordinary bilinear coefficients. -/

namespace Holant.Signature

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- The tensor product of the coordinate matrices, applied to a column signature. -/
def coordinateAction (A : Fin n → Bool → Bool → K) (f : Signature K n) : Signature K n :=
  fun x => ∑ y : Fin n → Bool, (∏ j : Fin n, A j (x j) (y j)) * f y

theorem prod_equality (x y : Fin n → Bool) :
    (∏ j : Fin n, equality (K := K) (x j) (y j)) = if x = y then 1 else 0 := by
  simp only [equality, Fintype.prod_boole, ← funext_iff]

@[simp] theorem coordinateAction_equality (f : Signature K n) :
    coordinateAction (fun _ => equality) f = f := by
  funext x
  simp [coordinateAction, prod_equality]

@[simp] theorem coordinateAction_zero (A : Fin n → Bool → Bool → K) :
    coordinateAction A (0 : Signature K n) = 0 := by
  funext x
  simp [coordinateAction]

theorem coordinateAction_add (A : Fin n → Bool → Bool → K) (f g : Signature K n) :
    coordinateAction A (f + g) = coordinateAction A f + coordinateAction A g := by
  funext x
  simp [coordinateAction, mul_add, Finset.sum_add_distrib]

/-- Tensor products of matrices compose by genuine multiplication at each ordered slot.
The proof exchanges the two full assignment sums, then distributes each slot sum. -/
theorem coordinateAction_comp (A B : Fin n → Kernel K) (f : Signature K n) :
    coordinateAction A (coordinateAction B f) =
      coordinateAction (fun j => Kernel.mul (A j) (B j)) f := by
  funext x
  simp only [coordinateAction, Kernel.mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- A separately supplied inverse identity at every slot cancels the two actions.
Only the displayed orientation of the inverse is required. -/
theorem coordinateAction_cancel (A B : Fin n → Kernel K)
    (hAB : ∀ j, Kernel.mul (A j) (B j) = equality) (f : Signature K n) :
    coordinateAction A (coordinateAction B f) = f := by
  rw [coordinateAction_comp]
  simpa only [hAB] using coordinateAction_equality f

/-- With no boundary slots, the action preserves the actual scalar. -/
@[simp] theorem coordinateAction_scalar (A : Fin 0 → Kernel K) (c : K) :
    coordinateAction A (scalar c) = scalar c := by
  funext x
  simp [coordinateAction, scalar]

end Holant.Signature
