import Holant.Platonic.StabilizerLine.Program

/-! A normalization program is constructed from the original tensor's actual
finite support equations and phase. The exterior scale is retained explicitly. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem NormalForm.dephase_translate {u : Signature ℂ n} (A : NormalForm u) :
    translateAction A.shift (phaseAction A.phase true u)=
      fun x => if vectorWord x∈A.direction then A.scalar else 0 := by
  funext x
  simp only [translateAction,phaseAction,phaseExponent,Bool.true_eq,ite_true]
  rw [A.exact_value]
  simp only [add_sub_cancel_right,fourthRootPhase_neg]
  by_cases hx : vectorWord x∈A.direction
  · rw [if_pos hx,if_pos hx]
    have hz : (fourthRootPhase (A.phase.eval (wordVector (vectorWord x+A.shift))):ℂ)≠0 := by
      exact_mod_cast fourthRootPhase_ne_zero _
    push_cast
    field_simp
  · rw [if_neg hx,if_neg hx,mul_zero]

theorem exists_normalizing_program (u : Signature ℂ n) (hu : ComplexAffine u) (hun : u≠0) :
    ∃ (P : Program n) (α : ℂ),α≠0 ∧ P.run u=fun x => α*delta x := by
  obtain ⟨A⟩ := hu.normalForm hun
  obtain ⟨r,s,e,hr,hn,he⟩ := exists_adapted_coordinates A.direction
  let P : Program n := .comp (.hadamard r s e) (.comp (.translate A.shift) (.phase A.phase true))
  refine ⟨P,((sqrtTwo⁻¹^r:AlgebraicComplex):ℂ)*(2:ℂ)^r*A.scalar,?_,?_⟩
  · apply mul_ne_zero _ A.scalar_ne_zero
    apply mul_ne_zero _ (pow_ne_zero _ (by norm_num))
    exact_mod_cast pow_ne_zero r (inv_ne_zero sqrtTwo_ne_zero)
  · change blockWalsh e (translateAction A.shift (phaseAction A.phase true u))=_
    rw [A.dephase_translate,blockWalsh_indicator A.direction e he]

theorem SharpSupport.scale_iff (f : Signature ℂ n) (c : ℂ) (hc : c≠0) :
    SharpSupport (fun x => c*f x) ↔ SharpSupport f := by
  have he (x : BinaryVector n) : (fun x => c*f x) (wordVector x)≠0 ↔ f (wordVector x)≠0 := by
    exact mul_ne_zero_iff.trans (and_iff_right hc)
  simp only [SharpSupport,he]

theorem program_sharp_line (u v : Signature ℂ n) (hu : ComplexAffine u) (hun : u≠0)
    (hv : ComplexAffine v) (hvn : v≠0) (c : ℂ) (hc : c≠0)
    (hw : ComplexAffine (fun x => u x+c*v x)) (hwn : (fun x => u x+c*v x)≠0) :
    ∃ (P : Program n) (α : ℂ),α≠0 ∧ P.run u=(fun x => α*delta x) ∧ SharpSupport (P.run v) := by
  obtain ⟨P,α,hα,hPu⟩ := exists_normalizing_program u hu hun
  let v' : Signature ℂ n := fun x => α⁻¹*P.run v x
  have hv' : ComplexAffine v' := (P.affine v hv).scale _
  have hvn' : v'≠0 := by
    intro h
    apply P.nonzero v hvn
    funext x
    have hh := congrFun h x
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hα)
  have he : (fun x => α⁻¹*P.run (fun x => u x+c*v x) x)=fun x => delta x+c*v' x := by
    have hp := P.linear u v 1 c
    simp only [one_mul] at hp
    funext x
    rw [hp,hPu]
    dsimp [v']
    field_simp
  have hw' : ComplexAffine (fun x => delta x+c*v' x) := by
    rw [←he]
    exact (P.affine _ hw).scale _
  have hwn' : (fun x => delta x+c*v' x)≠0 := by
    rw [←he]
    intro h
    apply P.nonzero _ hwn
    funext x
    have hh := congrFun h x
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hα)
  refine ⟨P,α,hα,hPu,?_⟩
  apply (SharpSupport.scale_iff (P.run v) α⁻¹ (inv_ne_zero hα)).mp
  exact normalized_sharp_support v' hv' hvn' c hc hw' hwn'

end
end Holant.Platonic.StabilizerLine
