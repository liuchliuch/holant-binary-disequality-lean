import Holant.Marked.SupportAtlas.Pencil

/-! Weighted sector edges turn current-group transfers into coset-valued
binary pencils. Analytic row normalization preserves every endpoint zero. -/
noncomputable section
namespace Holant.Marked.SupportAtlas
open Holant.Projective

def diagonalC (d : ℂ) : CMat := fun a b => if a = b then (if a then d else 1) else 0

def rowScale (d : ℂ) (M : CMat) : CMat := fun a b => (if a then d else 1) * M a b

/-- A safe sector binary has a current-group monomial transfer through its weighted edge. -/
def SafeWeighted (m : ℕ) (d : ℂ) (M : CMat) : Prop :=
  M = 0 ∨ IsRootMonomial m (Kernel.mul M (diagonalC d))

theorem rowScale_zero_iff (d : ℂ) (hd : d ≠ 0) (M : CMat) (a b : Bool) :
    rowScale d M a b = 0 ↔ M a b = 0 := by cases a <;> simp [rowScale, hd]

theorem rowScale_pencil (d : ℂ) (A B : CMat) (t : ℂ) :
    rowScale d (binaryPencil A B t) = binaryPencil (rowScale d A) (rowScale d B) t := by
  funext a b; cases a <;> simp [rowScale, binaryPencil] <;> ring

/-- The off-diagonal quotient changes by d², which is a root of unity in both source sectors. -/
theorem weighted_normalization {m : ℕ} (d : ℂ) (hd : d ≠ 0) (hdroot : (d^2)^m = 1)
    (M : CMat) (h : IsRootMonomial m (Kernel.mul M (diagonalC d))) :
    IsRootMonomial m (rowScale d M) := by
  simp only [IsRootMonomial, Kernel.mul_apply, diagonalC, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte, mul_zero, zero_mul, mul_one, add_zero, zero_add,
    rowScale, one_mul] at *
  rcases h with ⟨h01,h10,h00,h11,hr⟩ | ⟨h00,h11,h01,h10,hr⟩
  · left
    refine ⟨(mul_eq_zero.mp h01).resolve_right hd, by simpa [h10], h00, ?_, ?_⟩
    · exact mul_ne_zero hd ((mul_ne_zero_iff.mp h11).1)
    · simpa [mul_comm] using hr
  · right
    refine ⟨h00, by simpa [hd] using h11, (mul_ne_zero_iff.mp h01).1,
      mul_ne_zero hd h10, ?_⟩
    have he : d * M true false / M false true =
        d^2 * (M true false / (M false true * d)) := by field_simp
    rw [he, mul_pow, hdroot, hr, one_mul]

/-- Only zero-equivalence is used when transporting the endpoint support rule. -/
theorem matrixPattern_congr {A B C D : CMat}
    (hA : ∀ a b, A a b = 0 ↔ C a b = 0)
    (hB : ∀ a b, B a b = 0 ↔ D a b = 0) (h : MatrixPattern A B) :
    MatrixPattern C D := by
  obtain ⟨r,hz,hp⟩ := h
  refine ⟨r, ?_, ?_⟩
  · intro a b c hn
    cases a
    · exact (hA b c).mp (hz false b c hn)
    · exact (hB b c).mp (hz true b c hn)
  · have he : (fun (a b : Bool) => nonzeroBit (if a then B b (b ^^ r) else A b (b ^^ r))) =
        (fun (a b : Bool) => nonzeroBit (if a then D b (b ^^ r) else C b (b ^^ r))) := by
      funext a b
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · simp [nonzeroBit, hA]
      · simp [nonzeroBit, hB]
    rwa [← he]

/-- The three-phase classification remains exact in either weighted marked sector. -/
theorem matrixPattern_of_weighted_samples {m : ℕ} (hm : 3 ≤ m)
    (d : ℂ) (hd : d ≠ 0) (hdroot : (d^2)^m = 1) (A B : CMat)
    (h : ∀ t : ℂ, t^m=1 → SafeWeighted m d (binaryPencil A B t)) : MatrixPattern A B := by
  apply matrixPattern_congr (fun a b => rowScale_zero_iff d hd A a b)
    (fun a b => rowScale_zero_iff d hd B a b)
  apply matrixPattern_of_samples hm
  intro t ht
  rcases h t ht with hz | hm
  · left; rw [← rowScale_pencil, hz]; funext a b; simp [rowScale]
  · right; rw [← rowScale_pencil]; exact weighted_normalization d hd hdroot _ hm

theorem matrixPattern_unscale {A B : CMat} {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    (h : MatrixPattern (c • A) (d • B)) : MatrixPattern A B :=
  matrixPattern_congr (by intro a b; simp [hc]) (by intro a b; simp [hd]) h

end Holant.Marked.SupportAtlas
