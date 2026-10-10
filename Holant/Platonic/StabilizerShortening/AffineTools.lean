import Holant.Platonic.StabilizerLine.Program

/-! Literal complex affine closure for the coefficient operations in a
physical card. These are semantic facts; they add no realizable gadgets. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

theorem affine_zero_complex : ComplexAffine (0 : Signature ℂ n) := by
  exact ⟨0,0,affine_zero n,by simp⟩

theorem affine_complex_mul {f g : Signature ℂ n}
    (hf : ComplexAffine f) (hg : ComplexAffine g) : ComplexAffine (fun x => f x*g x) := by
  obtain ⟨a,u,hu,he⟩ := hf
  obtain ⟨b,v,hv,hvex⟩ := hg
  exact ⟨a*b,fun x=>u x*v x,hu.mul hv,by intro x;dsimp;rw [he,hvex];push_cast;ring⟩

theorem affine_complex_precompose {f : Signature ℂ n} (hf : ComplexAffine f)
    (p : Word m → Word n) (hp : IsAffineMap p) : ComplexAffine (fun x=>f (p x)) := by
  obtain ⟨c,g,hg,he⟩ := hf
  exact ⟨c,fun x=>g (p x),hg.precompose p hp,fun x=>he (p x)⟩

theorem affine_complex_scale_iff (c : ℂ) (hc : c≠0) (f : Signature ℂ n) :
    ComplexAffine (fun x=>c*f x) ↔ ComplexAffine f := by
  constructor
  · intro h
    have hh := h.scale c⁻¹
    simpa [←mul_assoc,hc] using hh
  · intro h;exact h.scale c

theorem affine_complex_inverse {f : Signature ℂ n} (hf : ComplexAffine f)
    (hn : ∀x,f x≠0) : ComplexAffine (fun x => (f x)⁻¹) := by
  have hfn : f≠0 := by intro h;exact hn (origin n) (by simp [h])
  obtain ⟨A⟩ := hf.normalForm hfn
  have he (x : Word n) : f x=A.scalar*(fourthRootPhase (A.phase.eval x):ℂ) := by
    have h := A.exact_value (vectorWord x)
    have hs := (A.support (vectorWord x)).mp (by simpa using hn x)
    simpa [hs] using h
  have hp : Affine (fun x => fourthRootPhase (-A.phase.eval x)) := by
    apply affine_phase_of_thirdDifference
    intro z u v w
    have h := thirdDifference_mul_const (-1) A.phase.eval z u v w
    simpa only [neg_one_mul,quadratic_thirdDifference,mul_zero] using h
  refine ⟨A.scalar⁻¹,_,hp,?_⟩
  intro x
  dsimp
  rw [he,mul_inv,fourthRootPhase_neg]
  push_cast
  rfl

end
end Holant.Platonic.StabilizerShortening
