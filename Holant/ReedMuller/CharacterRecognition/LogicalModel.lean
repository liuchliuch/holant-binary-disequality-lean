import Holant.ReedMuller.CharacterRecognition.MixedDirection
import Holant.ReedMuller.CharacterRecognition.Restriction
import Holant.ReedMuller.AffineRadon.NormalForm
import Holant.Tractable.AffineOperations
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual coordinates on an affine support. These are mathematical coordinate
maps, not primitive gadgets. Both the original algebraic coefficients and the
ambient sign character are reconstructed explicitly. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {r n : ℕ}

def supportEmbedding (D : BinaryCode n) (e : BinaryVector r ≃ₗ[ZMod 2] D) :
    BinaryVector r →ₗ[ZMod 2] BinaryVector n := D.subtype.comp e.toLinearMap

def logicalCoefficient (f : Signature AlgebraicComplex n) (a : BinaryVector n)
    (D : BinaryCode n) (e : BinaryVector r ≃ₗ[ZMod 2] D) : Signature AlgebraicComplex r :=
  fun x => f (wordVector (a+supportEmbedding D e (vectorWord x)))

theorem logicalCoefficient_nonzero (f : Signature AlgebraicComplex n) (A : ActualNormalForm f)
    (e : BinaryVector r ≃ₗ[ZMod 2] A.direction) (x : Word r) :
    logicalCoefficient f A.shift A.direction e x≠0 := by
  apply (A.support f _).mpr
  change A.shift+(e (vectorWord x)).val-A.shift∈A.direction
  simpa only [add_sub_cancel_left] using (e (vectorWord x)).property

theorem logicalCoefficient_affine (f : Signature AlgebraicComplex n) (hf : Affine f)
    (a : BinaryVector n) (D : BinaryCode n) (e : BinaryVector r ≃ₗ[ZMod 2] D) :
    Affine (logicalCoefficient f a D e) :=
  hf.precompose (AffinePatching.affineBoolean a (supportEmbedding D e))
    (AffinePatching.affineBoolean_isAffine a (supportEmbedding D e))

/-- The pulled-back quadratic and its scalar are derived from the actual
source affine formula; no phase representation is added as an input. -/
theorem logicalCoefficient_phase (f : Signature AlgebraicComplex n) (hf : Affine f)
    (A : ActualNormalForm f) (e : BinaryVector r ≃ₗ[ZMod 2] A.direction) :
    ∃ (c : AlgebraicComplex) (Q : QuadraticPhase r),c≠0 ∧ ∀ x,
      logicalCoefficient f A.shift A.direction e x=c*fourthRootPhase (Q.eval x) := by
  have ha := logicalCoefficient_affine f hf A.shift A.direction e
  rcases ha with hz|⟨c,hc,S,Q,he⟩
  · have hn := logicalCoefficient_nonzero f A e (origin r)
    exact False.elim (hn (congrFun hz _))
  refine ⟨c,Q,hc,?_⟩
  intro x
  have hn := logicalCoefficient_nonzero f A e x
  have hs : S.Holds x := by
    by_contra h
    apply hn
    rw [he]
    simp [affineFormula,h]
  rw [he]
  simp only [affineFormula,hs,ite_true]

/-- A character proved in actual support coordinates extends to an ambient
linear character. The affine shift contributes its exact sign to the scalar. -/
theorem cFlat_of_logical_character (f : Signature ℂ n) (a : BinaryVector n)
    (D : BinaryCode n) (hD : SelfDual D) (e : BinaryVector r ≃ₗ[ZMod 2] D)
    (hs : ∀ x,f (wordVector x)≠0 ↔ x-a∈D)
    (c : ℂ) (hc : c≠0) (ell : Character r)
    (he : ∀ x,f (wordVector (a+supportEmbedding D e (vectorWord x)))=
      c*sign (ell (vectorWord x))) : NonzeroFlat f := by
  obtain ⟨L,hL⟩ := (ell.comp e.symm.toLinearMap).exists_extend
  have hLe (x : BinaryVector r) : L (supportEmbedding D e x)=ell x := by
    have H := LinearMap.congr_fun hL (e x)
    simpa only [supportEmbedding,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply,Submodule.subtype_apply] using H
  let c' : ℂ := c*sign (L a)
  have hc' : c'≠0 := mul_ne_zero hc (sign_nonzero _)
  refine ⟨Units.mk0 c' hc',a,D,L,hD,?_⟩
  funext x
  change f x=if vectorWord x-a∈D then c'*sign (L (vectorWord x)) else 0
  by_cases hx : vectorWord x-a∈D
  · rw [if_pos hx]
    let t := e.symm ⟨vectorWord x-a,hx⟩
    have het : supportEmbedding D e t=vectorWord x-a := by
      change (e (e.symm ⟨vectorWord x-a,hx⟩)).val=vectorWord x-a
      rw [LinearEquiv.apply_symm_apply]
    have hh := he (wordVector t)
    simp only [vector_word,het,add_sub_cancel,word_vector] at hh
    rw [hh]
    have hl : L (vectorWord x)=L a+ell t := by
      rw [←hLe t,het,map_sub]
      abel
    rw [hl,sign_add]
    change c*sign (ell t)=(c*sign (L a))*(sign (L a)*sign (ell t))
    linear_combination -(c*sign (ell t))*(sign_square (L a))
  · rw [if_neg hx]
    have hn : ¬f x≠0 := by
      intro hn
      apply hx
      exact (hs (vectorWord x)).mp (by simpa using hn)
    exact not_ne_iff.mp hn

end
end Holant.ReedMuller.CharacterRecognition
