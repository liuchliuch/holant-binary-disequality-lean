import Holant.Platonic.RankDeficientLocalization.Normalization.StandardOutputs
import Holant.Certificates.RainbowOrbit.GeneratedOrbit

/-! Current-coordinate octahedral cards, pulled back only for coefficient
classification.  Matching labels and mixedness are proved to survive. -/
namespace Holant.Platonic.RankDeficientLocalization.Normalization
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.RainbowOrbit Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Form := OctahedralSeparator.Form
abbrev unmarkMap := PlatonicBridgeInterface.Octahedral.unmarkMap
abbrev coefficientEquiv := PlatonicBridgeInterface.Octahedral.coefficientEquiv
abbrev thetaEquiv := PlatonicBridgeInterface.Octahedral.thetaEquiv

def MarkedCone (f : Form) (F : FourTensor) : Prop := F=0 ∨ ∃r : Fin 3,MarkedInMatching f r F

theorem coefficientEquiv_act (f : Form) (F : FourTensor) :
    coefficientEquiv f F=act (markLegs f) F := rfl

theorem theta_representative (f : Form) (i : Fin 24) :
    thetaEquiv f (representative .octahedral i)=markedRepresentative f i := by
  change OctahedralSeparator.complexTheta f (representative .octahedral i)=_
  rw [show representative .octahedral i=OctahedralSeparator.complexMatrix
    (OctahedralSeparator.standard i) from octahedralRaw_standard i]
  exact (OctahedralSeparator.complexMatrix_theta f _).symm

theorem unmark_matching (f : Form) (r : Fin 3) (F : FourTensor)
    (hF : MarkedInMatching f r F) :
    InMatching .octahedral r ((coefficientEquiv f).symm F) := by
  obtain ⟨H,hH,hhe⟩ := matching_mark_surjective f r F hF
  have he : coefficientEquiv f H=F := hhe
  rw [←he,LinearEquiv.symm_apply_apply]
  exact hH

theorem unmark_cards (f : Form) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hc : ∀i,MarkedCone f (Φ (markedRepresentative f i))) :
    ∀i,matchingCone .octahedral (unmarkMap f Φ (representative .octahedral i)) := by
  intro i
  change matchingCone .octahedral ((coefficientEquiv f).symm (Φ (thetaEquiv f (representative .octahedral i))))
  rw [theta_representative]
  rcases hc i with hz|⟨r,hr⟩
  · rw [hz,map_zero]
    exact Or.inl rfl
  · obtain ⟨U,V,hU,hV,he⟩ := unmark_matching f r _ hr
    rw [he,matchingTensor_eq_product]
    exact matchingProduct_mem_cone .octahedral r hU hV

theorem markedCone_card (f : Form) (F : FourTensor) (hF : MarkedCone f F) :
    F=0 ∨ Nonempty (NonsingularCard F) := by
  rcases hF with hz|⟨r,U,V,hU,hV,rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨fourCard r U V hU.det_ne_zero hV.det_ne_zero⟩

theorem unmark_mixed (f : Form) (Φ : Mat →ₗ[ℂ] FourTensor)
    (hc : ∀i,MarkedCone f (Φ (markedRepresentative f i)))
    (hm : MixedCards Φ (markedRepresentative f)) :
    MixedCards (unmarkMap f Φ) (representative .octahedral) := by
  obtain ⟨i,j,D,E,hDE⟩ := hm
  obtain ⟨r,U,V,hU,hV,hF⟩ := (hc i).resolve_left D.nonzero
  obtain ⟨s,S,T,hS,hT,hH⟩ := (hc j).resolve_left E.nonzero
  have hD := card_matching_of_tensor D hU.det_ne_zero hV.det_ne_zero hF
  have hE := card_matching_of_tensor E hS.det_ne_zero hT.det_ne_zero hH
  have hrs : r≠s := by intro he; exact hDE (hD.trans (he ▸ hE.symm))
  have hi := unmark_matching f r _ ⟨U,V,hU,hV,hF⟩
  have hj := unmark_matching f s _ ⟨S,T,hS,hT,hH⟩
  obtain ⟨U',V',hU',hV',hF'⟩ := hi
  obtain ⟨S',T',hS',hT',hH'⟩ := hj
  have hif : unmarkMap f Φ (representative .octahedral i)=matchingTensor r U' V' := by
    change (coefficientEquiv f).symm (Φ (thetaEquiv f (representative .octahedral i)))=_
    rw [theta_representative]
    exact hF'
  have hjf : unmarkMap f Φ (representative .octahedral j)=matchingTensor s S' T' := by
    change (coefficientEquiv f).symm (Φ (thetaEquiv f (representative .octahedral j)))=_
    rw [theta_representative]
    exact hH'
  have ci := fourCard r U' V' (groupDirection_det_ne_zero .octahedral hU')
    (groupDirection_det_ne_zero .octahedral hV')
  have cj := fourCard s S' T' (groupDirection_det_ne_zero .octahedral hS')
    (groupDirection_det_ne_zero .octahedral hT')
  let ci' : NonsingularCard (unmarkMap f Φ (representative .octahedral i)) := hif ▸ ci
  let cj' : NonsingularCard (unmarkMap f Φ (representative .octahedral j)) := hjf ▸ cj
  refine ⟨i,j,ci',cj',?_⟩
  intro he
  have hiM := card_matching_of_tensor ci' (groupDirection_det_ne_zero .octahedral hU')
    (groupDirection_det_ne_zero .octahedral hV') hif
  have hjM := card_matching_of_tensor cj' (groupDirection_det_ne_zero .octahedral hS')
    (groupDirection_det_ne_zero .octahedral hT') hjf
  exact hrs (fourMatching_injective (hiM.symm.trans (he.trans hjM)))

theorem unmark_rank (f : Form) (Φ : Mat →ₗ[ℂ] FourTensor) :
    Module.finrank ℂ (unmarkMap f Φ).range=Module.finrank ℂ Φ.range := by
  have h := PlatonicBridgeInterface.Octahedral.markMap_rank f (unmarkMap f Φ)
  rw [PlatonicBridgeInterface.Octahedral.mark_unmark,
    PlatonicBridgeInterface.Octahedral.mapRank_eq_finrank,
    PlatonicBridgeInterface.Octahedral.mapRank_eq_finrank] at h
  exact h.symm

end
end Holant.Platonic.RankDeficientLocalization.Normalization
