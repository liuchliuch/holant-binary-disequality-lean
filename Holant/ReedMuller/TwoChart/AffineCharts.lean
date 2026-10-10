import Holant.ReedMuller.CharacterRecognition.SourceAPI
import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! Exact affine equations for arbitrary binary cosets and character phases.
These bridge the existing character-flat class to the original algebraic
Affine predicate used by the two-chart localization statements. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.CharacterRecognition
open Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

/-- Construct finite affine equations for the exact coset, without a supplied
support-system witness. -/
theorem exists_coset_system (a : BinaryVector n) (D : BinaryCode n) :
    ∃ S : AffineSystem n,∀ x,S.Holds x ↔ vectorWord x-a∈D := by
  obtain ⟨C,hC⟩ := D.exists_isCompl
  let P : BinaryVector n →ₗ[ZMod 2] BinaryVector n := C.projection D hC.symm
  let p := affineBoolean (-P a) P
  have hp := affineBoolean_isAffine (-P a) P
  refine ⟨(originSystem n).pullback p,?_⟩
  intro x
  rw [AffineSystem.pullback_holds _ p hp,originSystem_holds]
  have hv : vectorWord (p x)=P (vectorWord x-a) := by
    simp only [p,affineBoolean,vector_word,map_sub]
    abel
  constructor
  · intro h
    apply (C.projection_apply_eq_zero_iff hC.symm).mp
    change P (vectorWord x-a)=0
    rw [←hv,h,vector_origin]
  · intro h
    apply vector_injective
    rw [hv,vector_origin]
    exact (C.projection_apply_eq_zero_iff hC.symm).mpr h

 theorem affine_linear_sign (ell : Character n) :
    Affine (fun x => fourthRootPhase (evenLift (ell (vectorWord x)))) := by
  apply affine_phase_of_thirdDifference
  intro z u v w
  simp only [thirdDifference,vector_xor,map_add]
  generalize ell (vectorWord z)=a
  generalize ell (vectorWord u)=b
  generalize ell (vectorWord v)=c
  generalize ell (vectorWord w)=d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

 theorem affine_coset_character (c : AlgebraicComplex) (a : BinaryVector n)
    (D : BinaryCode n) (ell : Character n) :
    Affine (fun x => if vectorWord x-a∈D then
      c*fourthRootPhase (evenLift (ell (vectorWord x))) else 0) := by
  obtain ⟨S,hS⟩ := exists_coset_system a D
  have h := ((affine_linear_sign ell).scale c).restrict S
  convert h using 1
  funext x
  simp only [hS]

 theorem affine_of_character_presentation (f : Signature AlgebraicComplex n)
    (c : AlgebraicComplex) (a : BinaryVector n) (D : BinaryCode n) (ell : Character n)
    (he : ∀ x,(f x:ℂ)=if vectorWord x-a∈D then
      (c:ℂ)*sign (ell (vectorWord x)) else 0) : Affine f := by
  have hh : f=(fun x => if vectorWord x-a∈D then
      c*fourthRootPhase (evenLift (ell (vectorWord x))) else 0) := by
    funext x
    apply Subtype.ext
    rw [he]
    by_cases hx : vectorWord x-a∈D
    · rw [if_pos hx,if_pos hx]
      change (c:ℂ)*sign (ell (vectorWord x))=(c:ℂ)*root (evenLift (ell (vectorWord x)))
      rw [root_evenLift]
    · rw [if_neg hx,if_neg hx]
      rfl
  rw [hh]
  exact affine_coset_character c a D ell

/-- Every algebraic character-flat input belongs to the actual source affine
class, with genuine finite equations and an actual modulo-four quadratic. -/
theorem affine_of_CFlat (f : Signature AlgebraicComplex n)
    (hf : CFlat (fun x => (f x:ℂ))) : Affine f := by
  by_cases hz : f=0
  · rw [hz];exact affine_zero n
  obtain ⟨c,a,D,ell,hc,hD,he⟩ := algebraic_character_witness f hz hf
  exact affine_of_character_presentation f c a D ell he

end
end Holant.ReedMuller.TwoChart
