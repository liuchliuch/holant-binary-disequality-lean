import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! Element-order distributions in the actual permutation groups A₄, S₄, A₅.
Finite predicates below are tied to `orderOf` before they are counted. -/
namespace Holant.Projective.FiniteGroupFacts

abbrev A4 := alternatingGroup (Fin 4)
abbrev S4 := Equiv.Perm (Fin 4)
abbrev A5 := alternatingGroup (Fin 5)

/-- A computable, exact order test, including minimality of the exponent. -/
def HasExactOrder {G : Type*} [Monoid G] (n : ℕ) (g : G) : Prop :=
  g ^ n = 1 ∧ ∀ k ∈ Finset.Ico 1 n, g ^ k ≠ 1

instance {G : Type*} [Monoid G] [DecidableEq G] (n : ℕ) (g : G) :
    Decidable (HasExactOrder n g) := inferInstanceAs (Decidable (_ ∧ _))

theorem hasExactOrder_iff {G : Type*} [Monoid G] (n : ℕ) (hn : 0 < n) (g : G) :
    HasExactOrder n g ↔ orderOf g = n := by
  constructor
  · rintro ⟨hp, hm⟩
    apply (orderOf_eq_iff hn).mpr
    exact ⟨hp, fun k hk hk' => hm k (Finset.mem_Ico.mpr ⟨hk', hk⟩)⟩
  · intro h
    constructor
    · simpa [h] using pow_orderOf_eq_one g
    · intro k hk
      exact pow_ne_one_of_lt_orderOf (by have := (Finset.mem_Ico.mp hk).1; omega)
        (by simpa [h] using (Finset.mem_Ico.mp hk).2)

/-- A count over group elements themselves, with no abstract multiplication table. -/
def orderCount (G : Type*) [Monoid G] [Fintype G] [DecidableEq G] (n : ℕ) : ℕ :=
  ((Finset.univ : Finset G).filter (HasExactOrder n)).card

theorem orderCount_eq {G : Type*} [Monoid G] [Fintype G] [DecidableEq G]
    (n : ℕ) (hn : 0 < n) :
    orderCount G n = Fintype.card {g : G // orderOf g = n} := by
  classical
  rw [Fintype.card_subtype]
  unfold orderCount
  congr 1
  ext g
  simp [hasExactOrder_iff n hn]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a4_order_distribution :
    orderCount A4 1 = 1 ∧ orderCount A4 2 = 3 ∧ orderCount A4 3 = 8 ∧
      orderCount A4 4 = 0 ∧ orderCount A4 5 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s4_order_distribution :
    orderCount S4 1 = 1 ∧ orderCount S4 2 = 9 ∧ orderCount S4 3 = 8 ∧
      orderCount S4 4 = 6 ∧ orderCount S4 5 = 0 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a5_order_distribution :
    orderCount A5 1 = 1 ∧ orderCount A5 2 = 15 ∧ orderCount A5 3 = 20 ∧
      orderCount A5 4 = 0 ∧ orderCount A5 5 = 24 := by decide +kernel


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a4_orders_exhaustive (g : A4) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  have h : ∀ g : A4, HasExactOrder 1 g ∨ HasExactOrder 2 g ∨ HasExactOrder 3 g := by
    decide +kernel
  simpa only [hasExactOrder_iff 1 (by omega), hasExactOrder_iff 2 (by omega),
    hasExactOrder_iff 3 (by omega)] using h g

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem s4_orders_exhaustive (g : S4) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 4 := by
  have h : ∀ g : S4, HasExactOrder 1 g ∨ HasExactOrder 2 g ∨
      HasExactOrder 3 g ∨ HasExactOrder 4 g := by decide +kernel
  simpa only [hasExactOrder_iff 1 (by omega), hasExactOrder_iff 2 (by omega),
    hasExactOrder_iff 3 (by omega), hasExactOrder_iff 4 (by omega)] using h g

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem a5_orders_exhaustive (g : A5) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5 := by
  have h : ∀ g : A5, HasExactOrder 1 g ∨ HasExactOrder 2 g ∨
      HasExactOrder 3 g ∨ HasExactOrder 5 g := by decide +kernel
  simpa only [hasExactOrder_iff 1 (by omega), hasExactOrder_iff 2 (by omega),
    hasExactOrder_iff 3 (by omega), hasExactOrder_iff 5 (by omega)] using h g

end Holant.Projective.FiniteGroupFacts
