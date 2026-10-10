import Holant.Signature

/-! Tensor product and bilinear contraction. No conjugation is used. -/

namespace Holant

namespace Tensor

variable {K ι κ ν : Type*}

/-- Ordered disjoint tensor product. Port order is encoded by the sum type. -/
def tensor [Mul K] (f : Tensor K ι) (g : Tensor K κ) : Tensor K (ι ⊕ κ) :=
  fun x => f (fun i => x (.inl i)) * g (fun j => x (.inr j))

@[simp] theorem tensor_apply [Mul K] (f : Tensor K ι) (g : Tensor K κ)
    (x : ι ⊕ κ → Bool) :
    tensor f g x = f (fun i => x (.inl i)) * g (fun j => x (.inr j)) := rfl

theorem tensor_assoc [Semigroup K] (f : Tensor K ι) (g : Tensor K κ) (h : Tensor K ν) :
    reindex (Equiv.sumAssoc ι κ ν) (tensor (tensor f g) h) = tensor f (tensor g h) := by
  funext x
  exact mul_assoc _ _ _

theorem tensor_comm [CommMagma K] (f : Tensor K ι) (g : Tensor K κ) :
    reindex (Equiv.sumComm ι κ) (tensor f g) = tensor g f := by
  funext x
  exact mul_comm _ _

@[simp] theorem tensor_zero_left [MulZeroClass K] (g : Tensor K κ) :
    tensor (0 : Tensor K ι) g = 0 := by
  funext x
  simp [tensor]

@[simp] theorem tensor_zero_right [MulZeroClass K] (f : Tensor K ι) :
    tensor f (0 : Tensor K κ) = 0 := by
  funext x
  simp [tensor]

theorem tensor_add_left [Distrib K] (f₁ f₂ : Tensor K ι) (g : Tensor K κ) :
    tensor (f₁ + f₂) g = tensor f₁ g + tensor f₂ g := by
  funext x
  exact add_mul _ _ _

theorem tensor_add_right [Distrib K] (f : Tensor K ι) (g₁ g₂ : Tensor K κ) :
    tensor f (g₁ + g₂) = tensor f g₁ + tensor f g₂ := by
  funext x
  exact mul_add _ _ _

end Tensor

namespace Signature

variable {K : Type*} [Semiring K] {n : ℕ}

/-- Binary equality, used for ordinary wires or as a literal signature. -/
def equality (a b : Bool) : K := if a = b then 1 else 0

/-- Binary disequality. It is distinct from equality even when used as a native edge. -/
def disequality (a b : Bool) : K := if a ≠ b then 1 else 0

/-- Close the first two port occurrences using a specified bilinear edge tensor. -/
def contract (E : Bool → Bool → K) (f : Signature K (n + 2)) : Signature K n :=
  fun x => ∑ a : Bool, ∑ b : Bool, E a b * f (Fin.cons a (Fin.cons b x))

theorem contract_equality (f : Signature K (n + 2)) (x : Fin n → Bool) :
    contract equality f x = f (Fin.cons false (Fin.cons false x)) +
      f (Fin.cons true (Fin.cons true x)) := by
  simp [contract, equality, add_comm]

theorem contract_disequality (f : Signature K (n + 2)) (x : Fin n → Bool) :
    contract disequality f x = f (Fin.cons false (Fin.cons true x)) +
      f (Fin.cons true (Fin.cons false x)) := by
  simp [contract, disequality, add_comm]

@[simp] theorem contract_zero (E : Bool → Bool → K) :
    contract E (0 : Signature K (n + 2)) = 0 := by
  funext x
  simp [contract]

theorem contract_add (E : Bool → Bool → K) (f g : Signature K (n + 2)) :
    contract E (f + g) = contract E f + contract E g := by
  funext x
  simp [contract, mul_add, Finset.sum_add_distrib]

/-- A unary edge connection is bilinear, not a Hermitian inner product. -/
def connect (E : Bool → Bool → K) (u v : Bool → K) : K :=
  ∑ a : Bool, ∑ b : Bool, E a b * u a * v b

theorem connect_equality (u v : Bool → K) :
    connect equality u v = u false * v false + u true * v true := by
  simp [connect, equality, add_comm]

theorem connect_disequality (u v : Bool → K) :
    connect disequality u v = u false * v true + u true * v false := by
  simp [connect, disequality, add_comm]

end Signature
end Holant
