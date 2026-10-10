import Holant.Marked.SupportAtlas.Boolean
import Holant.Projective.BinaryPencil

/-! Derivation of the finite support rules from actual sampled binary pencils.
The row normalization is analytic and preserves every zero; it is not a gadget. -/
noncomputable section
namespace Holant.Marked.SupportAtlas
open Holant.Projective

abbrev CMat := Kernel ℂ

def nonzeroBit (x : ℂ) : Bool := decide (x ≠ 0)
@[simp] theorem nonzeroBit_false (x : ℂ) : nonzeroBit x = false ↔ x = 0 := by simp [nonzeroBit]
@[simp] theorem nonzeroBit_true (x : ℂ) : nonzeroBit x = true ↔ x ≠ 0 := by simp [nonzeroBit]

/-- The six endpoint support patterns, independently of their nonzero coefficients. -/
def MatrixPattern (A B : CMat) : Prop := ∃ r : Bool,
  (∀ a b c : Bool, (b ^^ c) ≠ r → (if a then B b c else A b c) = 0) ∧
  AllowedPattern (fun a b => nonzeroBit (if a then B b (b ^^ r) else A b (b ^^ r)))

theorem rootMonomial_smul_iff (m : ℕ) (c : ℂ) (hc : c ≠ 0) (A : CMat) :
    IsRootMonomial m (c • A) ↔ IsRootMonomial m A := by
  simp [IsRootMonomial, Pi.smul_apply, smul_eq_mul, hc, mul_div_mul_left _ _ hc]

theorem pattern_zero : MatrixPattern (0 : CMat) 0 := by
  refine ⟨false, ?_, Or.inl ?_⟩ <;> simp [nonzeroBit]

/-- A nonzero root-monomial row and any scalar multiple give one or two full rows. -/
theorem pattern_multiple {m : ℕ} (A : CMat) (hA : IsRootMonomial m A) (s : ℂ) :
    MatrixPattern A (s • A) := by
  rcases hA with ⟨h01,h10,h00,h11,_⟩ | ⟨h00,h11,h01,h10,_⟩
  · refine ⟨false, ?_, ?_⟩
    · intro a b c h; cases a <;> cases b <;> cases c <;> simp_all
    · by_cases hs : s = 0
      · exact Or.inr (Or.inl (by simp [nonzeroBit, h00, h11, hs]))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [nonzeroBit, h00, h11, hs]))))
  · refine ⟨true, ?_, ?_⟩
    · intro a b c h; cases a <;> cases b <;> cases c <;> simp_all
    · by_cases hs : s = 0
      · exact Or.inr (Or.inl (by simp [nonzeroBit, h01, h10, hs]))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp [nonzeroBit, h01, h10, hs]))))

theorem allowedPattern_swap (M : Bool → Bool → Bool) (h : AllowedPattern M) :
    AllowedPattern (fun a b => M (!a) b) := by
  simp only [AllowedPattern, Bool.not_false, Bool.not_true] at *
  tauto

theorem pattern_swap {A B : CMat} (h : MatrixPattern A B) : MatrixPattern B A := by
  obtain ⟨r,hz,hp⟩ := h
  refine ⟨r, ?_, ?_⟩
  · intro a b c h; cases a
    · simpa using hz true b c h
    · simpa using hz false b c h
  · have he : (fun a b => nonzeroBit (if a then A b (b ^^ r) else B b (b ^^ r))) =
        (fun a b => nonzeroBit (if !a then B b (b ^^ r) else A b (b ^^ r))) := by
      funext a b; cases a <;> rfl
    rw [he]
    exact allowedPattern_swap _ hp

/-- There is always a nonzero sample multiplier on a polygon with at least three phases. -/
theorem exists_nonzero_multiplier {m : ℕ} (hm : 3 ≤ m) (s : ℂ) :
    ∃ t : ℂ, t ^ m = 1 ∧ 1 + t * s ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hh := affine_product_zero_on_rootPolygon hm 1 s 1 0 (by
    intro t ht; simp [hn t ht])
  rcases hh with h | h <;> exact one_ne_zero h.1

theorem pattern_proportional {m : ℕ} (hm : 3 ≤ m) (A B : CMat)
    (hs : ∀ t : ℂ, t ^ m = 1 → binaryPencil A B t = 0 ∨ IsRootMonomial m (binaryPencil A B t))
    (hprop : BinaryProportional A B) : MatrixPattern A B := by
  have forward (A : CMat) (s : ℂ)
      (hh : ∀ t : ℂ, t ^ m = 1 → binaryPencil A (s • A) t = 0 ∨
        IsRootMonomial m (binaryPencil A (s • A) t)) : MatrixPattern A (s • A) := by
    by_cases hA : A = 0
    · simpa [hA] using pattern_zero
    obtain ⟨t,ht,hn⟩ := exists_nonzero_multiplier hm s
    have he : binaryPencil A (s • A) t = (1+t*s) • A := by
      funext a b; simp [binaryPencil]; ring
    rcases hh t ht with hz | hmono
    · rw [he] at hz
      have : A = 0 := (smul_eq_zero.mp hz).resolve_left hn
      exact (hA this).elim
    · exact pattern_multiple A ((rootMonomial_smul_iff m _ hn A).mp (he ▸ hmono)) s
  rcases (binaryProportional_iff A B).mp hprop with ⟨s,rfl⟩ | ⟨s,rfl⟩
  · exact forward A s hs
  · apply pattern_swap
    apply forward B s
    intro t ht
    have ht0 : t ≠ 0 := by intro h; simp [h, show m ≠ 0 by omega] at ht
    have htinv : t⁻¹ ^ m = 1 := by simp [inv_pow, ht]
    have he : binaryPencil (s • B) B t⁻¹ = t⁻¹ • binaryPencil B (s • B) t := by
      funext a b; simp [binaryPencil]; field_simp; ring
    rcases hs t⁻¹ htinv with hz | hmono
    · left; rw [he] at hz; exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero ht0)
    · right; exact (rootMonomial_smul_iff m t⁻¹ (inv_ne_zero ht0) _).mp (he ▸ hmono)

/-- Every zero-safe sampled pencil has exactly one of the Boolean endpoint patterns. -/
theorem matrixPattern_of_samples {m : ℕ} (hm : 3 ≤ m) (A B : CMat)
    (hs : ∀ t : ℂ, t ^ m = 1 → binaryPencil A B t = 0 ∨ IsRootMonomial m (binaryPencil A B t)) :
    MatrixPattern A B := by
  rcases binary_pencil_classification_endpoints hm A B hs with h | ⟨p,c,t,hc,ht,h | h⟩
  · exact pattern_proportional hm A B hs h
  all_goals have ht0 : t ≠ 0 := by intro hz; simp [hz, show m ≠ 0 by omega] at ht
  · obtain ⟨rfl,rfl⟩ := h
    refine ⟨p, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩
    · intro a b d hn; cases p <;> cases a <;> cases b <;> cases d <;> simp_all [parityAxis]
    · cases p <;> simp [nonzeroBit, parityAxis, hc, ht0]
  · obtain ⟨rfl,rfl⟩ := h
    refine ⟨p, ?_, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))⟩
    · intro a b d hn; cases p <;> cases a <;> cases b <;> cases d <;> simp_all [parityAxis]
    · cases p <;> simp [nonzeroBit, parityAxis, hc, ht0]

end Holant.Marked.SupportAtlas
