import Holant.Dihedral.PolarizedDeterminant.Polynomial
import Holant.Certificates.MatchingProductBridge.SwapRank

/-! Literal normalized physical cards from equation `app-nd-polarized-card`.
The two unused phase coordinates have exponent zero; all remaining coordinates
retain their original indices and their independently specified nonzero cosets. -/
noncomputable section
namespace Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators
open MvPolynomial

/-- Assignments to the remaining coordinates, extended by zero at the two exposed ones. -/
def sliceWords {s : ℕ} (i k : Fin s) : Finset (Cube s) :=
  Finset.univ.filter fun z => z i = false ∧ z k = false

@[simp] theorem mem_sliceWords {s : ℕ} (i k : Fin s) (z : Cube s) :
    z ∈ sliceWords i k ↔ z i = false ∧ z k = false := by simp [sliceWords]

def insert {s : ℕ} (i k : Fin s) (a xi : Bool) (z : Cube s) : Cube s :=
  Function.update (Function.update z i a) k xi

def cardPolynomial {s : ℕ} (w : Cube s → ℂ) (i k : Fin s)
    (a b xi : Bool) : MvPolynomial (Fin s) ℂ :=
  cubePolynomial (sliceWords i k) (fun z => w (insert i k a xi z) * w (insert i k b xi z))

/-- The actual two-copy coefficient sum, after removing its recorded nonzero scalar. -/
def card {s : ℕ} (w : Cube s → ℂ) (i k : Fin s) (lam : Fin s → ℂ)
    (a b xi : Bool) : ℂ :=
  ∑ z ∈ sliceWords i k, phaseMonomial lam z *
    w (insert i k a xi z) * w (insert i k b xi z)

@[simp] theorem eval_cardPolynomial {s : ℕ} (w : Cube s → ℂ) (i k : Fin s)
    (lam : Fin s → ℂ) (a b xi : Bool) :
    eval lam (cardPolynomial w i k a b xi) = card w i k lam a b xi := by
  simp [cardPolynomial, eval_cubePolynomial, card, mul_assoc]

/-- The three actual one-coordinate matrix rank conditions, with all four columns. -/
structure ThreeRanks (q : Bool → Bool → Bool → ℂ) : Prop where
  first : Matrix.rank (fun a : Bool => fun t : Bool × Bool => q a t.1 t.2) ≤ 1
  second : Matrix.rank (fun b : Bool => fun t : Bool × Bool => q t.1 b t.2) ≤ 1
  third : Matrix.rank (fun xi : Bool => fun t : Bool × Bool => q t.1 t.2 xi) ≤ 1

/-- All cards on the full coset grid satisfy all three flattening rank conditions. -/
def GridRanks {s : ℕ} (m : ℕ) (c : Fin s → ℂˣ) (w : Cube s → ℂ) : Prop :=
  ∀ (i k : Fin s), i ≠ k → ∀ z : Fin s → rootsOfUnity m ℂ,
    ThreeRanks (card w i k (fun j => (↑(c j * (z j).val) : ℂ)))

/-- The cross-slice minor from the first flattening, with the source's exact indices. -/
def gamma {s : ℕ} (w : Cube s → ℂ) (i k : Fin s) : MvPolynomial (Fin s) ℂ :=
  cardPolynomial w i k false false false * cardPolynomial w i k true false true -
  cardPolynomial w i k false false true * cardPolynomial w i k true false false

theorem gamma_eval_zero {s : ℕ} (w : Cube s → ℂ) (i k : Fin s)
    (lam : Fin s → ℂ) (h : ThreeRanks (card w i k lam)) : eval lam (gamma w i k) = 0 := by
  have hm := Holant.Certificates.MatchingProductBridge.minor_two_eq_zero_of_rank_le_one
    (fun a : Bool => fun t : Bool × Bool => card w i k lam a t.1 t.2)
    h.first false true (false, false) (false, true)
  simpa [gamma] using hm

theorem gamma_eq_zero {s m : ℕ} (hm : 3 ≤ m) (c : Fin s → ℂˣ)
    (w : Cube s → ℂ) (h : GridRanks m c w) (i k : Fin s) (hik : i ≠ k) :
    gamma w i k = 0 := by
  apply Holant.Laurent.polynomial_eq_zero_of_coset_grid hm c
  · intro j
    exact difference_products_degree _ _ _ _ _ j
  · intro z
    exact gamma_eval_zero w i k _ (h i k hik z)

/-- Only the ordered pair `(z,z)` contributes to the coefficient at `2z`.
This is the cross-slice relation omitted by a same-layer determinant alone. -/
theorem gamma_square_coefficient {s : ℕ} (w : Cube s → ℂ) (i k : Fin s)
    (z : Cube s) (hz : z ∈ sliceWords i k) :
    (gamma w i k).coeff (exponent z + exponent z) =
      w (insert i k false false z) * w (insert i k false true z) *
        (w (insert i k false false z) * w (insert i k true true z) -
         w (insert i k true false z) * w (insert i k false true z)) := by
  simp only [gamma, MvPolynomial.coeff_sub, cardPolynomial, square_coefficient _ _ _ z hz]
  ring

theorem face_identity {s m : ℕ} (hm : 3 ≤ m) (c : Fin s → ℂˣ)
    (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0) (h : GridRanks m c w)
    (i k : Fin s) (hik : i ≠ k) (z : Cube s) (hz : z ∈ sliceWords i k) :
    w (insert i k false false z) * w (insert i k true true z) =
      w (insert i k true false z) * w (insert i k false true z) := by
  have hh := congrArg (fun p : MvPolynomial (Fin s) ℂ => p.coeff (exponent z + exponent z))
    (gamma_eq_zero hm c w h i k hik)
  rw [gamma_square_coefficient w i k z hz] at hh
  simp only [AddMonoidAlgebra.coeff_zero] at hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (mul_ne_zero (hw _) (hw _)))

end Holant.Dihedral.PolarizedDeterminant
