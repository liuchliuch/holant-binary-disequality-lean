import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Complex geometric entry into a strict pair-difference cone. This file
contains no spectral dominance claim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeEntryGeometry

/-- Failure of all three immediate pair-difference cones, in squared coefficients. -/
def Blocked (A B C : ℂ) : Prop :=
  ‖C‖ ≤ ‖A-B‖ ∧ ‖A‖ ≤ ‖B-C‖ ∧ ‖B‖ ≤ ‖C-A‖

def inner (A B : ℂ) : ℝ := A.re*B.re+A.im*B.im

def mass (A B C : ℂ) : ℝ := Complex.normSq A+Complex.normSq B+Complex.normSq C

def heron (A B C : ℂ) : ℝ :=
  2*(Complex.normSq A*Complex.normSq B+Complex.normSq B*Complex.normSq C+
    Complex.normSq C*Complex.normSq A)-
  ((Complex.normSq A)^2+(Complex.normSq B)^2+(Complex.normSq C)^2)

/-- Positive defect is exactly the squared strict cone after a two-copy stage. -/
def defect (A B C : ℂ) : ℝ :=
  16*Complex.normSq A*Complex.normSq B-Complex.normSq ((A+B)^2-C^2)

theorem blocked_rotate {A B C : ℂ} (h : Blocked A B C) : Blocked B C A :=
  ⟨h.2.1,h.2.2,h.1⟩

theorem normSq_sub (A B : ℂ) :
    Complex.normSq (A-B)=Complex.normSq A+Complex.normSq B-2*inner A B := by
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,inner]
  ring

theorem normSq_sum (A B C : ℂ) :
    Complex.normSq (A+B+C)=mass A B C+2*(inner A B+inner B C+inner C A) := by
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,inner,mass]
  ring

theorem gram_zero (A B C : ℂ) :
    Complex.normSq A*Complex.normSq B*Complex.normSq C+
      2*inner A B*inner B C*inner C A-
      Complex.normSq A*(inner B C)^2-Complex.normSq B*(inner C A)^2-
      Complex.normSq C*(inner A B)^2=0 := by
  simp only [Complex.normSq_apply,inner]
  ring

theorem heron_factor (A B C : ℂ) :
    heron A B C=(‖A‖+‖B‖+‖C‖)*(‖A‖+‖B‖-‖C‖)*
      (‖A‖-‖B‖+‖C‖)*(-‖A‖+‖B‖+‖C‖) := by
  unfold heron
  rw [←Complex.sq_norm,←Complex.sq_norm,←Complex.sq_norm]
  ring

theorem heron_nonneg {A B C : ℂ} (h : Blocked A B C) : 0≤heron A B C := by
  have hC := h.1.trans (norm_sub_le A B)
  have hA := h.2.1.trans (norm_sub_le B C)
  have hB := h.2.2.trans (norm_sub_le C A)
  rw [heron_factor]
  exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith))
    (by linarith)) (by linarith)

theorem blocked_squared {A B C : ℂ} (h : Blocked A B C) :
    Complex.normSq C ≤ Complex.normSq (A-B) ∧
    Complex.normSq A ≤ Complex.normSq (B-C) ∧
    Complex.normSq B ≤ Complex.normSq (C-A) := by
  simpa only [Complex.sq_norm] using
    And.intro (pow_le_pow_left₀ (norm_nonneg C) h.1 2)
      (And.intro (pow_le_pow_left₀ (norm_nonneg A) h.2.1 2)
        (pow_le_pow_left₀ (norm_nonneg B) h.2.2 2))

theorem mass_bound {A B C : ℂ} (h : Blocked A B C) :
    Complex.normSq (A+B+C)≤2*mass A B C := by
  obtain ⟨h1,h2,h3⟩ := blocked_squared h
  rw [normSq_sub] at h1 h2 h3
  rw [normSq_sum]
  unfold mass
  linarith

theorem equal_mass_heron {A B C : ℂ} (h : Blocked A B C)
    (heq : Complex.normSq (A+B+C)=2*mass A B C) :
    mass A B C*heron A B C=
      8*Complex.normSq A*Complex.normSq B*Complex.normSq C := by
  obtain ⟨h1,h2,h3⟩ := blocked_squared h
  rw [normSq_sub] at h1 h2 h3
  rw [normSq_sum] at heq
  unfold mass at heq
  have hi1 : inner A B=(Complex.normSq A+Complex.normSq B-Complex.normSq C)/2 := by linarith
  have hi2 : inner B C=(Complex.normSq B+Complex.normSq C-Complex.normSq A)/2 := by linarith
  have hi3 : inner C A=(Complex.normSq C+Complex.normSq A-Complex.normSq B)/2 := by linarith
  have hg := gram_zero A B C
  rw [hi1,hi2,hi3] at hg
  unfold mass heron
  nlinarith [hg]

theorem defect_sum (A B C : ℂ) :
    defect A B C+defect B C A+defect C A B=
      (Complex.normSq (A+B+C)-2*mass A B C)^2+4*heron A B C := by
  simp only [defect,mass,heron,Complex.normSq_apply,pow_two,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im]
  ring

theorem defect_sum_pos {A B C : ℂ} (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (h : Blocked A B C) : 0<defect A B C+defect B C A+defect C A B := by
  rw [defect_sum]
  have hH := heron_nonneg h
  have hs := sq_nonneg (Complex.normSq (A+B+C)-2*mass A B C)
  by_contra hn
  have heq : Complex.normSq (A+B+C)=2*mass A B C := by nlinarith
  have hzero : heron A B C=0 := by nlinarith
  have hh := equal_mass_heron h heq
  rw [hzero,mul_zero] at hh
  have hp := mul_pos (mul_pos (Complex.normSq_pos.mpr hA) (Complex.normSq_pos.mpr hB))
    (Complex.normSq_pos.mpr hC)
  nlinarith

theorem blocked_ne {A B C : ℂ} (hC : C≠0) (h : Blocked A B C) : A≠B := by
  intro heq
  have hpos := norm_pos_iff.mpr hC
  have hh := h.1
  rw [heq,sub_self,norm_zero] at hh
  linarith

theorem zero_sum_other_defects {A B C : ℂ} (hz : A+B=0) :
    defect B C A+defect C A B=
      2*Complex.normSq C*(12*Complex.normSq A-Complex.normSq C) := by
  have heq : B=-A := by linear_combination hz
  rw [heq]
  simp only [defect,Complex.normSq_apply,pow_two,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im]
  ring

theorem zero_sum_good_pair {A B C : ℂ} (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (h : Blocked A B C) (hz : A+B=0) :
    (B+C≠0 ∧ 0<defect B C A) ∨ (C+A≠0 ∧ 0<defect C A B) := by
  have hBC : B+C≠0 := by
    intro hh
    have heq : C=A := by linear_combination hh-hz
    exact blocked_ne hB (blocked_rotate (blocked_rotate h)) heq
  have hCA : C+A≠0 := by
    intro hh
    have heq : B=C := by linear_combination hz-hh
    exact blocked_ne hA (blocked_rotate h) heq
  have heq : B=-A := by linear_combination hz
  have hdif : Complex.normSq (A-B)=4*Complex.normSq A := by
    rw [heq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.neg_re,Complex.neg_im]
    ring
  have hbnd := (blocked_squared h).1
  rw [hdif] at hbnd
  have hpA := Complex.normSq_pos.mpr hA
  have hpC := Complex.normSq_pos.mpr hC
  have hp : 0<2*Complex.normSq C*(12*Complex.normSq A-Complex.normSq C) :=
    mul_pos (by positivity) (by linarith)
  have hs := zero_sum_other_defects (C:=C) hz
  by_cases hpBC : 0<defect B C A
  · exact Or.inl ⟨hBC,hpBC⟩
  · exact Or.inr ⟨hCA,by linarith⟩

/-- One of the three pair choices has a nonzero middle coefficient and
strictly positive cone defect. -/
theorem good_pair {A B C : ℂ} (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (h : Blocked A B C) :
    (A+B≠0 ∧ 0<defect A B C) ∨
    (B+C≠0 ∧ 0<defect B C A) ∨
    (C+A≠0 ∧ 0<defect C A B) := by
  by_cases hAB : A+B=0
  · exact Or.inr (zero_sum_good_pair hA hB hC h hAB)
  by_cases hBC : B+C=0
  · rcases zero_sum_good_pair hB hC hA (blocked_rotate h) hBC with hc | ha
    · exact Or.inr (Or.inr hc)
    · exact Or.inl ha
  by_cases hCA : C+A=0
  · rcases zero_sum_good_pair hC hA hB (blocked_rotate (blocked_rotate h)) hCA with ha | hb
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
  have hs := defect_sum_pos hA hB hC h
  by_cases hpAB : 0<defect A B C
  · exact Or.inl ⟨hAB,hpAB⟩
  by_cases hpBC : 0<defect B C A
  · exact Or.inr (Or.inl ⟨hBC,hpBC⟩)
  exact Or.inr (Or.inr ⟨hCA,by linarith⟩)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeEntryGeometry
