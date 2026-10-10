import Holant.Certificates.RainbowOrbit.MarkedTransport

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def MarkedInMatching (f : Form) (r : Fin 3) (F : FourTensor) : Prop :=
  ∃ U V : BinaryMatrix,Direction f U ∧ Direction f V ∧ F=matchingTensor r U V

theorem theta_direction (f : Form) {U : BinaryMatrix} (hU : groupDirection .octahedral U) :
    Direction f (complexTheta f U) := (direction_iff_source_conjugate f _).mpr ⟨U,hU,rfl⟩

theorem matching_mark_forward (f : Form) (r : Fin 3) (F : FourTensor)
    (hF : InMatching .octahedral r F) : MarkedInMatching f r (act (markLegs f) F) := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hF
  have hm : ∀{A B : BinaryMatrix},groupDirection .octahedral A→groupDirection .octahedral B→
      groupDirection .octahedral (A*B) := RainbowOrbit.groupDirection_mul .octahedral
  fin_cases r
  · exact ⟨_,_,theta_direction f hU,theta_direction f hV,mark_P0 f U V⟩
  · exact ⟨_,_,theta_direction f (hm hU (markSinv_source f)),
      theta_direction f (hm (markS_source f) hV),mark_P1 f U V⟩
  · exact ⟨_,_,theta_direction f hU,
      theta_direction f (hm (hm (markS_source f) hV) (markSinv_source f)),mark_P2 f U V⟩

theorem matching_mark_surjective (f : Form) (r : Fin 3) (F : FourTensor)
    (hF : MarkedInMatching f r F) :
    ∃H, InMatching .octahedral r H ∧ act (markLegs f) H=F := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hF
  obtain ⟨U',hU',rfl⟩ := (direction_iff_source_conjugate f U).mp hU
  obtain ⟨V',hV',rfl⟩ := (direction_iff_source_conjugate f V).mp hV
  have hm : ∀{A B : BinaryMatrix},groupDirection .octahedral A→groupDirection .octahedral B→
      groupDirection .octahedral (A*B) := RainbowOrbit.groupDirection_mul .octahedral
  fin_cases r
  · exact ⟨P0 U' V',⟨_,_,hU',hV',rfl⟩,mark_P0 f U' V'⟩
  · refine ⟨P1 ((Matrix.of U')*markS f) (markSinv f*(Matrix.of V')),
      ⟨_,_,hm hU' (markS_source f),hm (markSinv_source f) hV',rfl⟩,?_⟩
    rw [mark_P1]
    simp only [mul_assoc,markS_mul_markSinv,mul_one]
    rw [←mul_assoc (markS f),markS_mul_markSinv,one_mul]
    rfl
  · refine ⟨P2 U' (markSinv f*(Matrix.of V')*markS f),
      ⟨_,_,hU',hm (hm (markSinv_source f) hV') (markS_source f),rfl⟩,?_⟩
    rw [mark_P2]
    simp only [mul_assoc,markS_mul_markSinv,mul_one]
    rw [←mul_assoc (markS f),markS_mul_markSinv,one_mul]
    rfl

theorem matching_mark_iff (f : Form) (r : Fin 3) (F : FourTensor) :
    MarkedInMatching f r (act (markLegs f) F) ↔ InMatching .octahedral r F := by
  constructor
  · intro h
    obtain ⟨H,hH,he⟩ := matching_mark_surjective f r _ h
    have hh : H=F := actionLinear_injective (markLegs f) (markLegs_det f) he
    simpa [hh] using hH
  · exact matching_mark_forward f r F

def markedDeck (f : Form) : Finset Point :=
  (deck .octahedral).map ⟨pointAction (markLegs f) (markLegs_det f),pointAction_injective _ _⟩

theorem markedDeck_card (f : Form) : (markedDeck f).card=1728 := by
  simp [markedDeck,deck_card,size]

def MarkedDeckPoint (f : Form) (p : Point) : Prop :=
  ∃ r F, ∃hF : F≠0, MarkedInMatching f r F ∧ p=Projectivization.mk ℂ F hF

theorem markedDeck_iff_mem (f : Form) (p : Point) : MarkedDeckPoint f p ↔ p∈markedDeck f := by
  classical
  constructor
  · rintro ⟨r,F,hF,hM,rfl⟩
    obtain ⟨H,hH,he⟩ := matching_mark_surjective f r F hM
    have hH0 : H≠0 := by intro hz; apply hF; rw [←he,hz]; simp [act]
    have hm : Projectivization.mk ℂ H hH0∈deck .octahedral := by
      apply (inDeck_iff_mem .octahedral H hH0).mp
      obtain ⟨U,V,hU,hV,rfl⟩ := hH
      exact ⟨r,U,V,hU,hV,Proportional.refl _⟩
    refine Finset.mem_map.mpr ⟨_,hm,?_⟩
    simp only [Function.Embedding.coeFn_mk,pointAction_mk]
    congr 1
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    induction q using Projectivization.ind with | h F hF =>
    obtain ⟨r,U,V,hU,hV,⟨c,hc,he⟩⟩ := (inDeck_iff_mem .octahedral F hF).mpr hq
    have hmatch : InMatching .octahedral r F :=
      ⟨c • U,V,groupDirection_smul .octahedral hU hc,hV,
        he.trans (matchingTensor_smul_left r c U V).symm⟩
    exact ⟨r,_,_,matching_mark_forward f r F hmatch,rfl⟩

end
end Holant.Certificates.RainbowOrbit
