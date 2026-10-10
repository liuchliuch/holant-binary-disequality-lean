import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! The signed-contraction induction step of MWX Lemma 47. Real collinearity
is expressed by a determinant, including zero-vector cases. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionCore

def area (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re
def Collinear (a b : ℂ) : Prop := area a b = 0

theorem area_polarization (a b c d : ℂ) :
    area (a+c) (b+d) + area (a-c) (b-d) = 2*(area a b+area c d) := by
  simp only [area, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  ring

theorem area_scale (t a b : ℂ) :
    area (t*a) (t*b) = Complex.normSq t * area a b := by
  simp only [area, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem collinear_scale_iff (t a b : ℂ) (ht : t≠0) :
    Collinear (t*a) (t*b) ↔ Collinear a b := by
  simp only [Collinear, area_scale, mul_eq_zero,
    (Complex.normSq_eq_zero.not.mpr ht), false_or]

theorem collinear_reversed_difference (a b c d : ℂ) :
    Collinear (c-a) (d-b) ↔ Collinear (a-c) (b-d) := by
  have h : area (c-a) (d-b)=area (a-c) (b-d) := by
    simp only [area, Complex.sub_re, Complex.sub_im]
    ring
  simp only [Collinear, h]

theorem collinear_zero_left (a : ℂ) : Collinear 0 a := by simp [Collinear, area]
theorem collinear_zero_right (a : ℂ) : Collinear a 0 := by simp [Collinear, area]

theorem noncollinear_nonzero {a b : ℂ} (h : ¬Collinear a b) : a≠0 ∧ b≠0 := by
  constructor
  · rintro rfl
    exact h (collinear_zero_left b)
  · rintro rfl
    exact h (collinear_zero_right a)

theorem collinear_div_im (a b : ℂ) (hb : b≠0) :
    Collinear a b ↔ (a/b).im=0 := by
  have hd : (a/b).im= -area a b / Complex.normSq b := by
    rw [Complex.div_im]
    unfold area
    ring
  simp only [hd, Collinear, div_eq_zero_iff, neg_eq_zero,
    (Complex.normSq_eq_zero.not.mpr hb), or_false]

theorem collinear_trans {a b c : ℂ} (hc : c≠0)
    (hac : Collinear a c) (hcb : Collinear c b) : Collinear a b := by
  have hid : area a b * Complex.normSq c =
      area a c * (c.re*b.re+c.im*b.im) +
        (a.re*c.re+a.im*c.im)*area c b := by
    simp only [area, Complex.normSq_apply]
    ring
  change area a c=0 at hac
  change area c b=0 at hcb
  rw [hac,hcb,mul_zero,zero_mul,add_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_right (Complex.normSq_eq_zero.not.mpr hc)

theorem noncollinear_through {a b c : ℂ} (hab : ¬Collinear a b) (hc : c≠0) :
    ¬Collinear a c ∨ ¬Collinear c b := by
  by_contra h
  push Not at h
  exact hab (collinear_trans hc h.1 h.2)

theorem signed_pair_area {a b c d : ℂ}
    (hp : Collinear (a+c) (b+d)) (hm : Collinear (a-c) (b-d)) :
    area a b + area c d = 0 := by
  have h := area_polarization a b c d
  change area (a+c) (b+d)=0 at hp
  change area (a-c) (b-d)=0 at hm
  linarith

theorem six_signed_contractions_collinear (a b c d e f : ℂ)
    (hacp : Collinear (a+c) (b+d)) (hacm : Collinear (a-c) (b-d))
    (haep : Collinear (a+e) (b+f)) (haem : Collinear (a-e) (b-f))
    (hcep : Collinear (c+e) (d+f)) (hcem : Collinear (c-e) (d-f)) :
    Collinear a b ∧ Collinear c d ∧ Collinear e f := by
  have h₁ := signed_pair_area hacp hacm
  have h₂ := signed_pair_area haep haem
  have h₃ := signed_pair_area hcep hcem
  unfold Collinear
  exact ⟨by linarith, by linarith, by linarith⟩

theorem noncollinear_signed_contraction (a b c d e f : ℂ)
    (h : ¬Collinear a b) :
    ¬Collinear (a+c) (b+d) ∨ ¬Collinear (a-c) (b-d) ∨
    ¬Collinear (a+e) (b+f) ∨ ¬Collinear (a-e) (b-f) ∨
    ¬Collinear (c+e) (d+f) ∨ ¬Collinear (c-e) (d-f) := by
  by_contra hn
  push Not at hn
  exact h (six_signed_contractions_collinear a b c d e f
    hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2).1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionCore
