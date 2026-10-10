import Holant.OrderedTensor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Hamming layers, charge, central restriction, and one-hot support predicates. -/

namespace Holant

/-- Hamming weight in the fixed port order. -/
def weight {n : ℕ} (x : Fin n → Bool) : ℕ :=
  ∑ i : Fin n, if x i then 1 else 0

@[simp] theorem weight_zero (x : Fin 0 → Bool) : weight x = 0 := by simp [weight]

theorem weight_le {n : ℕ} (x : Fin n → Bool) : weight x ≤ n := by
  calc
    weight x ≤ ∑ _ : Fin n, 1 := Finset.sum_le_sum (fun i _ => by cases x i <;> decide)
    _ = n := by simp

theorem weight_compl_add {n : ℕ} (x : Fin n → Bool) :
    weight (fun i => !(x i)) + weight x = n := by
  unfold weight
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i : Fin n, ((if !(x i) then 1 else 0) + if x i then 1 else 0)) =
        ∑ _ : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      cases x i <;> rfl
    _ = n := by simp

/-- The doubled charge, so every arity has an integer-valued charge. -/
def charge {n : ℕ} (x : Fin n → Bool) : ℤ := 2 * (weight x : ℤ) - n

theorem charge_compl {n : ℕ} (x : Fin n → Bool) :
    charge (fun i => !(x i)) = -charge x := by
  have h := weight_compl_add x
  unfold charge
  omega

namespace Signature

variable {K : Type*} [Zero K] {n d : ℕ}

/-- Support on one specified Hamming layer; the zero signature is permitted. -/
def SingleLayer (f : Signature K n) (d : ℕ) : Prop :=
  ∀ x, weight x ≠ d → f x = 0

/-- One-hot support includes weight zero, matching the manuscript's class M. -/
def OneHot (f : Signature K n) : Prop := ∀ x, 1 < weight x → f x = 0

/-- Keep the central Hamming layer, setting every other entry to zero. -/
def centralRestriction (f : Signature K n) : Signature K n :=
  fun x => if 2 * weight x = n then f x else 0

@[simp] theorem centralRestriction_apply (f : Signature K n) (x : Fin n → Bool) :
    centralRestriction f x = if 2 * weight x = n then f x else 0 := rfl

@[simp] theorem centralRestriction_idempotent (f : Signature K n) :
    centralRestriction (centralRestriction f) = centralRestriction f := by
  funext x
  by_cases h : 2 * weight x = n <;> simp [centralRestriction, h]

theorem centralRestriction_odd (k : ℕ) (f : Signature K (2 * k + 1)) :
    centralRestriction f = 0 := by
  funext x
  have h : 2 * weight x ≠ 2 * k + 1 := by omega
  simp [centralRestriction, h]

theorem centralRestriction_singleLayer (f : Signature K (2 * d)) :
    SingleLayer (centralRestriction f) d := by
  intro x hx
  have h : 2 * weight x ≠ 2 * d := by omega
  simp [centralRestriction, h]

theorem singleLayer_unique {f : Signature K n} (hf : f ≠ 0)
    {a b : ℕ} (ha : SingleLayer f a) (hb : SingleLayer f b) : a = b := by
  classical
  by_contra hab
  apply hf
  funext x
  by_cases hxa : weight x = a
  · exact hb x (by omega)
  · exact ha x hxa

end Signature
end Holant
