import Holant.ReedMuller.CharacterRecognition.Assembly
import Holant.ReedMuller.CharacterRecognition.SignedPhysical

/-! Source Lemma 7.24 and its literal fixed-graph/native-Bell consumer. The
original algebraic scalar is reconstructed, and no coordinate map is granted
as an additional primitive gadget. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem source_affine_to_character_radon_even {n : ℕ} (hn10 : 10≤n) (hnEven : _root_.Even n)
    (f : Signature AlgebraicComplex n) (hf : Affine f) (hn : f≠0)
    (hd : CFlatSignedRadonCards (fun x => (f (wordVector x):ℂ))) :
    CFlat (fun x => (f x:ℂ)) := by
  obtain ⟨r,hr⟩ := hnEven
  rw [←two_mul] at hr
  subst n
  exact source_affine_to_character_radon (by omega) f hf hn hd

 theorem source_character_from_actual_networks {n : ℕ}
    (hn10 : 10≤n+2) (hnEven : _root_.Even (n+2))
    (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (f : Signature AlgebraicComplex (n+2)) (hf : Affine f) (hn : f≠0)
    (frames : (v : BinaryVector (n+2)) → Accessible v → RadonAccess.RadonFrame (n+2))
    (direction : ∀ v hv,(frames v hv).v=v)
    (graphs : ∀ v hv,SignedRadon.ActualGraph κ (frames v hv).A)
    (cards : ∀ v hv d l,CFlat
      (SignedRadon.signedNetwork (frames v hv) (graphs v hv) (fun x => (f x:ℂ)) d l).denote) :
    CFlat (fun x => (f x:ℂ)) := by
  apply source_affine_to_character_radon_even hn10 hnEven f hf hn
  intro v hv
  refine ⟨frames v hv,direction v hv,?_⟩
  intro d l
  exact SignedTransport.cflat_native_network_implies_actualSignedRadon hκ (frames v hv)
    (graphs v hv) (fun x => (f x:ℂ)) d l (cards v hv d l)

/-- The complex character-flat description of an algebraic signature has a
nonzero algebraic scalar, recovered from one original supported coefficient. -/
theorem algebraic_character_witness {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : f≠0) (hf : CFlat (fun x => (f x:ℂ))) :
    ∃ (c : AlgebraicComplex) (a : BinaryVector n) (D : BinaryCode n) (ell : Character n),
      c≠0 ∧ SelfDual D ∧ ∀ x,(f x:ℂ)=
        if vectorWord x-a∈D then (c:ℂ)*sign (ell (vectorWord x)) else 0 := by
  rcases hf with hz|⟨c,a,D,ell,hD,he⟩
  · apply False.elim
    apply hn
    funext x
    apply Subtype.ext
    exact congrFun hz x
  have ha : (f (wordVector a):ℂ)=(c:ℂ)*sign (ell a) := by
    have H := congrFun he (wordVector a)
    simpa only [signature,value,vector_word,sub_self,Submodule.zero_mem,ite_true] using H
  let ca : AlgebraicComplex := f (wordVector a)*fourthRootPhase (TwoTranslate.evenLift (ell a))
  have hca : (ca:ℂ)=(c:ℂ) := by
    change (f (wordVector a):ℂ)*root (TwoTranslate.evenLift (ell a))=(c:ℂ)
    rw [root_evenLift,ha,mul_assoc,sign_square,mul_one]
  have hc : ca≠0 := by
    intro h
    apply c.ne_zero
    rw [←hca,h]
    rfl
  refine ⟨ca,a,D,ell,hc,hD,?_⟩
  intro x
  rw [hca]
  exact congrFun he x

 theorem source_affine_to_character_algebraic {n : ℕ} (hn10 : 10≤n) (hnEven : _root_.Even n)
    (f : Signature AlgebraicComplex n) (hf : Affine f) (hn : f≠0)
    (hd : CFlatSignedRadonCards (fun x => (f (wordVector x):ℂ))) :
    ∃ (c : AlgebraicComplex) (a : BinaryVector n) (D : BinaryCode n) (ell : Character n),
      c≠0 ∧ SelfDual D ∧ ∀ x,(f x:ℂ)=
        if vectorWord x-a∈D then (c:ℂ)*sign (ell (vectorWord x)) else 0 :=
  algebraic_character_witness f hn (source_affine_to_character_radon_even hn10 hnEven f hf hn hd)

end
end Holant.ReedMuller.CharacterRecognition
