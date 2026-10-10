import Holant.ReedMuller.SignedRadon.Transition
import Holant.ReedMuller.SignedRadon.Network

/-! The final change-of-choice statement in literal physical boundary
coordinates, including both graph scales and the scalar part of the sign. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

def boundaryTransition (F G : RadonAccess.RadonFrame (n+2)) (h : F.v=G.v) (d : ZMod 2) :
    BinaryVector n ≃ᵃ[ZMod 2] BinaryVector n :=
  ((boundaryAffine F d).symm.trans (orbitChange F G h d)).trans (boundaryAffine G d)

theorem boundaryTransition_linear (F G : RadonAccess.RadonFrame (n+2))
    (h : F.v=G.v) (d : ZMod 2) (w : BinaryVector n) :
    (boundaryTransition F G h d).linear w=
      G.pairBoundaryLinearEquiv (transitionLinear F G h (F.pairBoundaryLinearEquiv.symm w)) := rfl

theorem boundaryTransition_isometry (F G : RadonAccess.RadonFrame (n+2))
    (h : F.v=G.v) (d : ZMod 2) (w z : BinaryVector n) :
    dot ((boundaryTransition F G h d).linear w) ((boundaryTransition F G h d).linear z)=dot w z := by
  rw [boundaryTransition_linear,boundaryTransition_linear,G.pairBoundaryLinearEquiv_isometry,
    transitionLinear_isometry]
  have H := F.pairBoundaryLinearEquiv_isometry (F.pairBoundaryLinearEquiv.symm w)
    (F.pairBoundaryLinearEquiv.symm z)
  simpa only [F.pairBoundaryLinearEquiv.apply_symm_apply] using H.symm

def boundaryCharacter (F G : RadonAccess.RadonFrame (n+2)) (l : ZMod 2) : Character n :=
  (choiceCharacter F G l).comp F.pairBoundaryLinearEquiv.symm.toLinearMap

def boundaryConstant (F G : RadonAccess.RadonFrame (n+2)) (d l : ZMod 2) : ZMod 2 :=
  choiceConstant F G d l+boundaryCharacter F G l (ones n)

theorem boundaryCard_transition (F G : RadonAccess.RadonFrame (n+2)) (h : F.v=G.v)
    (d l : ZMod 2) (g : Signature ℂ (n+2)) (x : BinaryVector n) :
    boundaryCard G d l g (wordVector (boundaryTransition F G h d x))=
      sign (boundaryConstant F G d l)*sign (boundaryCharacter F G l x)*
        boundaryCard F d l g (wordVector x) := by
  unfold boundaryCard
  rw [vector_word,vector_word]
  change signedCard G d l (fun z => g (wordVector z))
    ((boundaryAffine G d).symm ((boundaryAffine G d)
      (orbitChange F G h d ((boundaryAffine F d).symm x))))=_
  rw [AffineEquiv.symm_apply_apply,boundaryAffine_symm,signedCard_change]
  have hs : choiceCharacter F G l (F.pairBoundaryLinearEquiv.symm (x+ones n))=
      boundaryCharacter F G l x+boundaryCharacter F G l (ones n) := by
    exact (boundaryCharacter F G l).map_add x (ones n)
  rw [hs,boundaryConstant,sign_add,sign_add]
  ring

end RadonFrame

/-- Physical networks for any two recorded choices differ by an actual affine
isometry, a nonzero scalar, and one linear sign character. -/
theorem signedNetwork_change_choice {κ : ZMod 2 → ZMod 2 → ℂ}
    (F G : RadonAccess.RadonFrame (n+2)) (h : F.v=G.v)
    (ΓF : ActualGraph κ F.A) (ΓG : ActualGraph κ G.A)
    (g : Signature ℂ (n+2)) (d l : ZMod 2) :
    ∃ c : ℂ,c≠0 ∧ ∀ x : BinaryVector n,
      (signedNetwork G ΓG g d l).denote (wordVector (RadonFrame.boundaryTransition F G h d x))=
        c*sign (RadonFrame.boundaryCharacter F G l x)*
          (signedNetwork F ΓF g d l).denote (wordVector x) := by
  let c := (ΓG.scalar/ΓF.scalar)*sign (RadonFrame.boundaryConstant F G d l)
  refine ⟨c,mul_ne_zero (div_ne_zero ΓG.scalar_ne ΓF.scalar_ne) (sign_nonzero _),?_⟩
  intro x
  simp only [signedNetwork_denote,Pi.smul_apply,smul_eq_mul]
  rw [RadonFrame.boundaryCard_transition]
  dsimp only [c]
  field_simp [ΓF.scalar_ne]

end
end Holant.ReedMuller.SignedRadon
