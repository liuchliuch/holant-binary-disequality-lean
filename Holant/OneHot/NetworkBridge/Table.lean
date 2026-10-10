import Holant.Support

/-! Canonical one-hot signatures from their zero-word and singleton values. -/

namespace Holant.OneHot

variable {K : Type*} {n : ℕ}

/-- The local one-hot table with zero-word value `a` and singleton values `b`. -/
def table [CommSemiring K] (a : K) (b : Fin n → K) : Signature K n :=
  fun x => if weight x ≤ 1 then
    (if weight x = 0 then a else ∏ i, if x i then b i else 1) else 0

@[simp] theorem weight_false : weight (fun _ : Fin n => false) = 0 := by
  simp [weight]

@[simp] theorem weight_singleton (i : Fin n) :
    weight (fun j : Fin n => decide (j = i)) = 1 := by
  simp [weight]

theorem weight_eq_zero_iff (x : Fin n → Bool) :
    weight x = 0 ↔ ∀ i, x i = false := by
  simp [weight]

@[simp] theorem weight_cons (parent : Bool) (x : Fin n → Bool) :
    weight (Fin.cons parent x) = (if parent then 1 else 0) + weight x := by
  unfold weight
  rw [Fin.sum_univ_succ]
  simp

@[simp] theorem table_zero [CommSemiring K] (a : K) (b : Fin n → K) :
    table a b (fun _ => false) = a := by
  simp [table]

@[simp] theorem table_singleton [CommSemiring K] (a : K) (b : Fin n → K)
    (i : Fin n) : table a b (fun j => decide (j = i)) = b i := by
  simp [table]

/-- Every canonical table has one-hot support, including the zero word. -/
theorem table_oneHot [CommSemiring K] (a : K) (b : Fin n → K) :
    Signature.OneHot (table a b) := by
  intro x hx
  simp [table, Nat.not_le.mpr hx]

/-- Separate the parent port from the ordered child ports in a local table. -/
theorem table_cons [CommSemiring K] (a parentCoeff : K) (b : Fin n → K)
    (parent : Bool) (x : Fin n → Bool) :
    table a (Fin.cons parentCoeff b) (Fin.cons parent x) =
      if (if parent then 1 else 0) + weight x ≤ 1 then
        (if parent then parentCoeff else
          if weight x = 0 then a else ∏ i, if x i then b i else 1) else 0 := by
  cases parent
  · simp [table, Fin.prod_univ_succ]
  · by_cases h : weight x = 0
    · have hx := (weight_eq_zero_iff x).mp h
      simp [table, h, Fin.prod_univ_succ, hx]
    · have hweight : ¬1 + weight x ≤ 1 := by omega
      simp [table, hweight]

end Holant.OneHot
