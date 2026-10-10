import Holant.ReedMuller.CharacterRecognition.LogicalModel
import Holant.ReedMuller.CharacterRecognition.SignedCards

/-! Pull genuine signed quotient cards back to the actual support coordinates,
restoring their exact exterior linear sign. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r n : ℕ}

theorem full_character_of_actual_signed_card (g : BinaryVector n → ℂ)
    (a : BinaryVector n) (U : BinaryCode n) (hU : SelfDual U)
    (e : BinaryVector r ≃ₗ[ZMod 2] U) (F : RadonAccess.RadonFrame n) (hv : F.v∈U)
    (l : ZMod 2)
    (hc : CFlat (fun x => SignedTransport.actualSignedRadon F (dot a F.v) l g (vectorWord x)))
    (hs : ∀ x,g x+sign l*g (x+F.v)≠0 ↔ x-a∈U) :
    FullCharacter (fun t => g (a+supportEmbedding U e (vectorWord t))+
      sign l*g (a+supportEmbedding U e (vectorWord t)+F.v)) := by
  let E := supportEmbedding U e
  let P := (AffineRadon.RadonFrame.boundaryProjection F).comp E
  let z := AffineRadon.RadonFrame.boundaryProjection F a
  let card : Signature ℂ (n-2) := fun x =>
    SignedTransport.actualSignedRadon F (dot a F.v) l g (vectorWord x)
  let mu : Character r := l • ((SignedRadon.RadonFrame.selected F).comp E)
  let s : ℂ := sign (l*SignedRadon.RadonFrame.selected F a)
  have hp (t : BinaryVector r) : dot (a+E t) F.v=dot a F.v := by
    have hh : dot (E t) F.v=0 := (hU _).mp (e t).property F.v hv
    rw [dot_add_left,hh,add_zero]
  have he (t : BinaryVector r) : card (wordVector (z+P t))=
      sign (l*SignedRadon.RadonFrame.selected F (a+E t))*
        (g (a+E t)+sign l*g (a+E t+F.v)) := by
    change SignedTransport.actualSignedRadon F (dot a F.v) l g
      (vectorWord (wordVector (z+P t)))=_
    rw [vector_word]
    have hcoord : z+P t=AffineRadon.RadonFrame.boundaryProjection F (a+E t) := by
      simp only [z,P,LinearMap.comp_apply,map_add]
    rw [hcoord]
    exact SignedTransport.actualSignedRadon_projection F _ l g _ (hp t)
  have hn (x : Word r) (_ : True) : card (wordVector (z+P (vectorWord x)))≠0 := by
    rw [he]
    apply mul_ne_zero (sign_nonzero _)
    apply (hs _).mpr
    change a+(e (vectorWord x)).val-a∈U
    simpa only [add_sub_cancel_left] using (e (vectorWord x)).property
  obtain ⟨c,hcn,ell,hell⟩ := character_of_CFlat_restriction card hc
    (fun _ => True) (origin r) trivial P z s (sign_nonzero _) mu hn
  refine ⟨c,hcn,ell,?_⟩
  intro x
  have H := hell x trivial
  have hsign : s*sign (mu (vectorWord x))=
      sign (l*SignedRadon.RadonFrame.selected F (a+E (vectorWord x))) := by
    simp only [s,mu,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul,map_add,mul_add,sign_add]
  rw [hsign,he,←mul_assoc,sign_square,one_mul] at H
  exact H

end
end Holant.ReedMuller.CharacterRecognition
