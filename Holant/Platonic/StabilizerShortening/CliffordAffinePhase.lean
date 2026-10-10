import Holant.Platonic.StabilizerShortening.CliffordAffineSupport

/-! Quadratic phase of a one-dimensional Pauli fixed space, derived from
actual fixing operators and exact affine support coordinates. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n r s : ℕ}

/-- Every translation along the actual shift code has an affine Pauli derivative. -/
theorem fixed_phase_derivatives (f : Signature ℂ n) (x₀ : BinaryVector n)
    (M : BinaryVector r →ₗ[ZMod 2] BinaryVector n)
    (hM : ∀z,M z∈stabilizerShifts f) (u : BinaryVector r) :
    ∃q : ZMod 4,∃ell : BinaryVector r →ₗ[ZMod 2] ZMod 2,∀z,
      f (wordVector (x₀+M (z+u)))=
        phaseRoot q*sign (ell z)*f (wordVector (x₀+M z)) := by
  obtain ⟨P,hP,hshift⟩ := hM u
  refine ⟨P.phase+evenLift (P.character (x₀+M u)),P.character.comp M,?_⟩
  intro z
  have he := congrFun hP (wordVector (x₀+M (z+u)))
  have hx : x₀+M (z+u)+P.shift=x₀+M z := by
    rw [hshift,map_add]
    calc
      _ = (x₀+M z)+(M u+M u) := by abel
      _ = _ := by rw [binary_self,add_zero]
  simp only [Pauli.run,vector_word,hx] at he
  rw [←he,phaseRoot_add,phaseRoot_even]
  have hc : P.character (x₀+M (z+u))=P.character (x₀+M u)+(P.character.comp M) z := by
    simp only [map_add,LinearMap.comp_apply]
    abel
  rw [hc,sign_add]
  ring

def supportSystem (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r × BinaryVector s)
    (x₀ : BinaryVector n) : AffineSystem n where
  rows := s
  matrix i := characterLabel ((LinearMap.proj i).comp (rightCoordinates e))
  rhs := (e x₀).2

theorem supportSystem_holds
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector r × BinaryVector s)
    (x₀ : BinaryVector n) (w : Word n) :
    (supportSystem e x₀).Holds w ↔ (e (vectorWord w+x₀)).2=0 := by
  have hrow (i : Fin s) :
      (∑j,(supportSystem e x₀).matrix i j*bitValue (ZMod 2) (w j))=(e (vectorWord w)).2 i := by
    change dot (characterLabel ((LinearMap.proj i).comp (rightCoordinates e))) (vectorWord w)=_
    rw [characterLabel_dot]
    rfl
  dsimp only [supportSystem] at hrow
  simp only [AffineSystem.Holds,supportSystem,map_add,Prod.snd_add]
  simp_rw [hrow]
  constructor
  · intro h
    ext i
    change (e (vectorWord w)).2 i+(e x₀).2 i=0
    rw [h i]
    exact CharTwo.add_self_eq_zero _
  · intro h i
    have hh := congrFun h i
    change (e (vectorWord w)).2 i+(e x₀).2 i=0 at hh
    have hc := CharTwo.add_self_eq_zero ((e x₀).2 i)
    linear_combination hh-hc

/-- A literal one-dimensional Pauli fixed space is a member of the source affine
class. Both its support system and even-mixed quadratic phase are constructed. -/
theorem complexAffine_of_unique_fixed (f : Signature ℂ n) (hf : UniqueFixedLine f)
    (hn : f≠0) : ComplexAffine f := by
  have hex : ∃w,f w≠0 := by
    by_contra h
    apply hn
    ext w
    simpa using not_exists.mp h w
  obtain ⟨w₀,hw₀⟩ := hex
  let x₀ := vectorWord w₀
  have hx₀ : f (wordVector x₀)≠0 := by simpa [x₀] using hw₀
  obtain ⟨r,s,e,hr,hn,he⟩ := exists_adapted_coordinates (stabilizerShifts f)
  let M : BinaryVector r →ₗ[ZMod 2] BinaryVector n :=
    e.symm.toLinearMap.comp (LinearMap.inl (ZMod 2) (BinaryVector r) (BinaryVector s))
  have hM (z : BinaryVector r) : M z∈stabilizerShifts f := by
    apply (he _).mp
    simp [M]
  let a : BinaryVector r → ℂ := fun z => f (wordVector (x₀+M z))
  have ha (z : BinaryVector r) : a z≠0 := shift_support f x₀ hx₀ (M z) (hM z)
  obtain ⟨c,hc,Q,hQ⟩ := quadratic_of_affine_derivatives a ha
    (fixed_phase_derivatives f x₀ M hM)
  let p : Word n → Word r := affineBoolean ((e x₀).1) (leftCoordinates e)
  have hp (w : Word n) : p w=wordVector ((e (vectorWord w+x₀)).1) := by
    simp [p,affineBoolean,leftCoordinates,map_add,add_comm]
  let S := supportSystem e x₀
  let g : Signature AlgebraicComplex n := fun w =>
    if S.Holds w then fourthRootPhase (Q.eval (p w)) else 0
  have hg : Affine g := by
    exact ((affine_quadratic_phase Q).precompose p
      (affineBoolean_isAffine ((e x₀).1) (leftCoordinates e))).restrict S
  refine ⟨c,g,hg,?_⟩
  intro w
  by_cases hs : S.Holds w
  · have hs0 : (e (vectorWord w+x₀)).2=0 := (supportSystem_holds e x₀ w).mp hs
    have hm : M ((e (vectorWord w+x₀)).1)=vectorWord w+x₀ := by
      apply e.injective
      simp only [M,LinearMap.comp_apply,LinearMap.inl_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hs0.symm
    have hx : x₀+M ((e (vectorWord w+x₀)).1)=vectorWord w := by
      rw [hm]
      calc
        _ = (x₀+x₀)+vectorWord w := by abel
        _ = _ := by rw [binary_self,zero_add]
    have hv := hQ ((e (vectorWord w+x₀)).1)
    change f (wordVector (x₀+M ((e (vectorWord w+x₀)).1)))=_ at hv
    rw [hx,word_vector] at hv
    simpa [g,hs,hp] using hv
  · have hzero : f w=0 := by
      by_contra hw
      have hm := (unique_fixed_support f hf x₀ hx₀ (vectorWord w)).mp (by simpa using hw)
      have hz := (he _).mpr hm
      exact hs ((supportSystem_holds e x₀ w).mpr hz)
    simp [g,hs,hzero]

end
end Holant.Platonic.StabilizerShortening
