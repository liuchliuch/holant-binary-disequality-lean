import Holant.ReedMuller.DiagonalSlice.Three
import Mathlib.Analysis.Complex.Basic

/-! Source Lemma 7.8. The hypothesis is an actual product of arbitrary unary
functions on every equal-coordinate restriction. The conclusion is derived for
all nonzero coefficient tables, without assuming multiplicative interactions. -/
namespace Holant.ReedMuller.DiagonalSlice
open scoped BigOperators
variable {α G : Type*} [Fintype α] [DecidableEq α] [CommGroup G]

def word (S : Finset α) : α → Bool := fun i => decide (i ∈ S)
def support (x : α → Bool) : Finset α := Finset.univ.filter fun i => x i

def SimpleDiagonal (h : (α → Bool) → G) (i j : α) : Prop :=
  ∃ a : Bool → G, ∃ b : α → Bool → G, ∀ x : α → Bool,
    x i = x j → h x = a (x i) * ∏ k ∈ outside i j, b k (x k)

@[simp] theorem word_empty : word (∅ : Finset α) = fun _ => false := by funext i; simp [word]
@[simp] theorem word_univ : word (Finset.univ : Finset α) = fun _ => true := by funext i; simp [word]
@[simp] theorem word_support (x : α → Bool) : word (support x) = x := by
  funext i
  cases hi : x i <;> simp [word,support,hi]

theorem simple_table {h : (α → Bool) → G} {i j : α}
    (hs : SimpleDiagonal h i j) : Simple (fun S => h (word S)) i j := by
  obtain ⟨a,b,H⟩ := hs
  refine ⟨a,b,?_⟩
  intro S hS
  apply H (word S)
  simp only [word,hS]

/-- The first clause of Lemma 7.8, valid over every commutative group and hence
for the manuscript's nonzero complex coefficients. -/
theorem diagonal_slice_integration {r : ℕ} (hr : 4 ≤ r)
    (h : (Fin r → Bool) → G) (h0 : h (fun _ => false) = 1)
    (hs : ∀ i j, i ≠ j → SimpleDiagonal h i j) :
    ∃ rho : Fin r → G, ∀ x,
      h x = ∏ i, rho i ^ (if x i then 1 else 0 : ℕ) := by
  refine ⟨fun i => h (word {i}),?_⟩
  intro x
  have H := integrate (h := fun S => h (word S)) (by simpa using h0)
    (by simpa using hr) (fun i j hij => simple_table (hs i j hij)) (support x)
  rw [word_support] at H
  rw [H,support,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  cases hi : x i <;> simp [hi]

/-- The exact second clause of Lemma 7.8, including the common nonzero kappa. -/
theorem diagonal_slice_three
    (h : (Fin 3 → Bool) → G) (h0 : h (fun _ => false) = 1)
    (hs : ∀ i j, i ≠ j → SimpleDiagonal h i j) :
    ∃ rho : Fin 3 → G, ∃ kappa : G,
      (∀ i, h (word {i}) = rho i) ∧
      (∀ i j, i ≠ j → h (word {i,j}) = kappa * rho i * rho j) ∧
      h (fun _ => true) = kappa * rho 0 * rho 1 * rho 2 := by
  simpa using integrate_three (h := fun S => h (word S)) (by simpa using h0)
    (fun i j hij => simple_table (hs i j hij))

/-- Full source statement, with the original coefficient domain C^×. -/
theorem source_diagonal_slice_integration (r : ℕ) (_hr : 3 ≤ r)
    (h : (Fin r → Bool) → ℂˣ) (h0 : h (fun _ => false) = 1)
    (hs : ∀ i j, i ≠ j → SimpleDiagonal h i j) :
    (4 ≤ r → ∃ rho : Fin r → ℂˣ, ∀ x,
      h x = ∏ i, rho i ^ (if x i then 1 else 0 : ℕ)) ∧
    (∀ e : r = 3,
      ∃ rho : Fin 3 → ℂˣ, ∃ kappa : ℂˣ,
        (∀ i, h (fun k => word {i} (Fin.cast e k)) = rho i) ∧
        (∀ i j, i ≠ j → h (fun k => word {i,j} (Fin.cast e k)) = kappa * rho i * rho j) ∧
        h (fun _ => true) = kappa * rho 0 * rho 1 * rho 2) := by
  constructor
  · intro h4; exact diagonal_slice_integration h4 h h0 hs
  · intro e
    subst r
    simpa using diagonal_slice_three h h0 hs

end Holant.ReedMuller.DiagonalSlice
