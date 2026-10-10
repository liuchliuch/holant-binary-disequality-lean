import Holant.Partition

/-! Tensor products with the manuscript's original-port-first finite ordering. -/

namespace Holant.Signature

variable {K : Type*} {m n : ℕ}

/-- Concatenate two ordered blocks, putting every port of the first factor first. -/
def tensor [Mul K] (f : Signature K m) (g : Signature K n) : Signature K (m + n) :=
  Tensor.reindex finSumFinEquiv (Tensor.tensor f g)

@[simp] theorem tensor_apply [Mul K] (f : Signature K m) (g : Signature K n)
    (x : Fin (m + n) → Bool) :
    tensor f g x = f (fun i => x (Fin.castAdd n i)) *
      g (fun j => x (Fin.natAdd m j)) := rfl

/-- Summing a concatenated tensor preserves the product of the exact scalar sums. -/
theorem total_tensor [Semiring K] (f : Signature K m) (g : Signature K n) :
    Tensor.total (tensor f g) = Tensor.total f * Tensor.total g := by
  rw [tensor, Tensor.total_reindex, Tensor.total_tensor]

/-- A tensor power includes the zeroth power, whose value is the nullary unit. -/
def unaryPower [CommMonoid K] (u : Bool → K) (n : ℕ) : Signature K n :=
  fun x => ∏ i : Fin n, u (x i)

@[simp] theorem unaryPower_zero [CommMonoid K] (u : Bool → K) :
    unaryPower u 0 = scalar 1 := by
  funext x
  simp [unaryPower, scalar]

end Holant.Signature
