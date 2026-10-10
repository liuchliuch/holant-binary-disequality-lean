import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push

/-! Generic coordinate Segre equations, with arbitrary finite factor dimensions. -/
noncomputable section
namespace Holant.Platonic.FixedMatchingRuling.Segre
open scoped BigOperators
open Function
variable {M : Type*} [Fintype M] {κ : M → Type*}

/-- Coordinate arrays for a tensor with independently indexed factor bases. -/
abbrev Array (κ : M → Type*) := ((e : M) → κ e) → ℂ

/-- The coefficient array of a simple tensor. -/
def product (U : (e : M) → κ e → ℂ) : Array κ := fun x => ∏ e, U e (x e)

/-- All two-by-two minors of every one-factor flattening vanish. -/
def MinorsVanish [DecidableEq M] (A : Array κ) : Prop :=
  ∀ (e : M) (x y : (e : M) → κ e),
    A x * A y - A (update x e (y e)) * A (update y e (x e)) = 0

/-- Zero is included, allowing degenerate values of a linear family. -/
def IsPureOrZero (A : Array κ) : Prop := A = 0 ∨ ∃ U, A = product U

theorem product_update [DecidableEq M] (U : (e : M) → κ e → ℂ)
    (x : (e : M) → κ e) (e : M) (a : κ e) :
    product U (update x e a) = U e a * ∏ f ∈ Finset.univ.erase e, U f (x f) := by
  unfold product
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro f hf
  rw [update_of_ne (Finset.ne_of_mem_erase hf)]

theorem product_minors [DecidableEq M] (U : (e : M) → κ e → ℂ) :
    MinorsVanish (product U) := by
  intro e x y
  have hx := product_update U x e (x e)
  have hy := product_update U y e (y e)
  simp only [update_eq_self] at hx hy
  rw [hx, hy, product_update, product_update]
  ring

theorem pureOrZero_minors [DecidableEq M] {A : Array κ} (h : IsPureOrZero A) :
    MinorsVanish A := by
  rcases h with rfl | ⟨U, rfl⟩
  · intro e x y
    simp
  · exact product_minors U

/-- A nonzero pivot reconstructs every coefficient from its one-coordinate slices. -/
theorem pivot_formula [DecidableEq M] (A : Array κ) (h : MinorsVanish A)
    (p : (e : M) → κ e) (hp : A p ≠ 0) (x : (e : M) → κ e) :
    A x = A p * ∏ e, A (update p e (x e)) / A p := by
  have aux (s : Finset M) : ∀ x : (e : M) → κ e,
      (∀ e, e ∉ s → x e = p e) →
      A x = A p * ∏ e ∈ s, A (update p e (x e)) / A p := by
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      have he : x = p := funext (fun e => hx e (by simp))
      simp [he]
    | @insert e s hes ih =>
      intro x hx
      let y := update x e (p e)
      have hy : ∀ f, f ∉ s → y f = p f := by
        intro f hf
        by_cases hfe : f = e
        · subst f; simp [y]
        · simp only [y, update_of_ne hfe]
          exact hx f (by simp [hf, hfe])
      have hi := ih y hy
      have hm := sub_eq_zero.mp (h e x p)
      change A x * A p = A y * A (update p e (x e)) at hm
      have hprod : (∏ f ∈ s, A (update p f (y f)) / A p) =
          ∏ f ∈ s, A (update p f (x f)) / A p := by
        apply Finset.prod_congr rfl
        intro f hf
        have hfe : f ≠ e := fun hh => hes (hh ▸ hf)
        rw [show y f = x f from update_of_ne hfe _ _]
      rw [hprod] at hi
      rw [Finset.prod_insert hes]
      apply (mul_right_cancel₀ hp)
      rw [hm, hi]
      field_simp
  exact aux Finset.univ x (by simp)

/-- Multiplying one factor absorbs an arbitrary overall coefficient. -/
theorem product_smul_update [DecidableEq M] (U : (e : M) → κ e → ℂ)
    (e : M) (c : ℂ) : product (update U e (c • U e)) = c • product U := by
  funext x
  unfold product
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  simp only [update_self, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  have hh : (∏ f ∈ Finset.univ.erase e, update U e (c • U e) f (x f)) =
      ∏ f ∈ Finset.univ.erase e, U f (x f) := by
    apply Finset.prod_congr rfl
    intro f hf
    rw [update_of_ne (Finset.ne_of_mem_erase hf)]
  rw [hh]
  ring

/-- The actual Segre equations characterize the whole affine cone. -/
theorem minors_iff_pureOrZero [DecidableEq M] [Nonempty M] (A : Array κ) :
    MinorsVanish A ↔ IsPureOrZero A := by
  constructor
  · intro h
    by_cases hz : A = 0
    · exact Or.inl hz
    right
    have hp : ∃ p, A p ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hz (funext hn)
    obtain ⟨p, hp⟩ := hp
    let U : (e : M) → κ e → ℂ := fun e a => A (update p e a) / A p
    obtain ⟨e⟩ := ‹Nonempty M›
    refine ⟨update U e (A p • U e), ?_⟩
    rw [product_smul_update]
    funext x
    exact pivot_formula A h p hp x
  · exact pureOrZero_minors

end Holant.Platonic.FixedMatchingRuling.Segre
