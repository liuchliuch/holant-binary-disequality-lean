import Holant.Proofs.Hardness.GeneralEOPhaseExtractionCore
import Holant.Proofs.Hardness.GeneralEOARSBoundary

/-! Single real phase and a proved common complement sign imply genuine ARS
up to scale. Equal complementary norms are not substituted for the sign. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionStructure
open Holant
namespace C
export GeneralEOPhaseExtractionCore (Collinear collinear_div_im)
end C
namespace A
export GeneralEOARSBoundary (ARSUpToScale)
end A
namespace F
export SelfDualPinObstruction (flip)
end F
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def SinglePhase (f : Signature ℂ n) : Prop := ∀x y,C.Collinear (f x) (f y)

theorem normalize (f : Signature ℂ n) (hf : SinglePhase f) :
    ∃c : ℂ,c≠0 ∧ ∃r : Signature ℝ n,∀x,f x=c*(r x : ℂ) := by
  classical
  by_cases hz : ∀x,f x=0
  · exact ⟨1,one_ne_zero,fun _ => 0,by simp [hz]⟩
  push Not at hz
  obtain ⟨w,hw⟩ := hz
  refine ⟨f w,hw,fun x => (f x/f w).re,?_⟩
  intro x
  have hi : (f x/f w).im=0 := (C.collinear_div_im (f x) (f w) hw).mp (hf x w)
  have hr : ((f x/f w).re : ℂ)=f x/f w := by
    apply Complex.ext <;> simp [hi]
  rw [hr]
  exact (mul_div_cancel₀ (f x) hw).symm.trans (by ring)

theorem ars_of_complement_sign (f : Signature ℂ n) (hf : SinglePhase f)
    (hflip : (∀x,f (F.flip x)=f x) ∨ (∀x,f (F.flip x)= -f x)) :
    A.ARSUpToScale f := by
  obtain ⟨c,hc,r,hr⟩ := normalize f hf
  rcases hflip with hp|hm
  · refine ⟨c,hc,fun x => (r x : ℂ),?_,?_⟩
    · intro x
      have hx := hp x
      rw [hr,hr] at hx
      have hh := mul_left_cancel₀ hc hx
      simpa using hh
    · funext x
      exact hr x
  · refine ⟨-Complex.I*c,mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hc,
      fun x => Complex.I*(r x : ℂ),?_,?_⟩
    · intro x
      have hx := hm x
      rw [hr,hr,←mul_neg] at hx
      have hh := mul_left_cancel₀ hc hx
      change Complex.I*(r (F.flip x) : ℂ)=star (Complex.I*(r x : ℂ))
      rw [hh]
      simp
    · funext x
      change f x=(-Complex.I*c)*(Complex.I*(r x : ℂ))
      rw [hr]
      have hi := Complex.I_mul_I
      linear_combination (c*(r x : ℂ))*hi

theorem nonars_has_phase (f : Signature ℂ n)
    (hflip : (∀x,f (F.flip x)=f x) ∨ (∀x,f (F.flip x)= -f x))
    (hf : ¬A.ARSUpToScale f) : ∃x y,¬C.Collinear (f x) (f y) := by
  by_contra h
  push Not at h
  exact hf (ars_of_complement_sign f h hflip)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionStructure
