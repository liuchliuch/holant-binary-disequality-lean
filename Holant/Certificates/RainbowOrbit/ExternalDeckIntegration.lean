import Holant.Certificates.RainbowOrbit.NoRainbow
import Holant.Certificates.RainbowOrbit.ExternalSource

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace External

theorem matrixFamily : MatrixFamily Direction where
  one := direction_one
  mul := Direction.mul
  inverse := Direction.inverse
  transpose := Direction.transpose
  smul := Direction.smul
  nonsingular := Direction.det_ne_zero

abbrev DeckIndex := Fin 3 × Fin 12 × Fin 12

def deckPoint (i : DeckIndex) : Point :=
  Projectivization.mk ℂ (matchingTensor i.1 (representative i.2.1) (representative i.2.2))
    (matching_nonzero _ _ _ (representative_det_ne_zero _) (representative_det_ne_zero _))

theorem deckPoint_injective : Function.Injective deckPoint := by
  rintro ⟨r,i,j⟩ ⟨s,k,l⟩ he
  have hp := (proportional_point_iff _ _ _ _).mpr he
  have hrs := proportional_matching_labels r s _ _ _ _
    (representative_det_ne_zero _) (representative_det_ne_zero _)
    (representative_det_ne_zero _) (representative_det_ne_zero _) hp
  subst s
  obtain ⟨⟨c,hc,hi⟩,⟨d,hd,hj⟩⟩ := proportional_matching_factors r _ _ _ _
    (representative_det_ne_zero _) (representative_det_ne_zero _) hp
  have hik := projectively_injective i k c hi
  have hjl := projectively_injective j l d hj
  subst k; subst l
  rfl

def deck : Finset Point := by
  classical
  exact Finset.univ.map ⟨deckPoint,deckPoint_injective⟩

theorem deck_card : deck.card=432 := by
  classical
  simp [deck,DeckIndex]

def InMatching (r : Fin 3) (F : FourTensor) : Prop :=
  ∃ U V : BinaryMatrix,Direction U ∧ Direction V ∧ F=matchingTensor r U V

def DeckPoint (p : Point) : Prop :=
  ∃r F,∃hF : F≠0,InMatching r F ∧ p=Projectivization.mk ℂ F hF

theorem deckPoint_iff_mem (p : Point) : DeckPoint p ↔ p∈deck := by
  classical
  constructor
  · rintro ⟨r,F,hF,⟨U,V,⟨i,c,hc,hi⟩,⟨j,d,hd,hj⟩,rfl⟩,rfl⟩
    have hh := matching_proportional r ⟨c,hc,hi⟩ ⟨d,hd,hj⟩
    have he := (proportional_point_iff _ _ hF (matching_nonzero r _ _
      (representative_det_ne_zero i) (representative_det_ne_zero j))).mp hh
    change Projectivization.mk ℂ (matchingTensor r U V) hF=deckPoint (r,i,j) at he
    rw [he]
    exact Finset.mem_map.mpr ⟨(r,i,j),Finset.mem_univ _,rfl⟩
  · intro hm
    obtain ⟨⟨r,i,j⟩,_,rfl⟩ := Finset.mem_map.mp hm
    exact ⟨r,_,_,⟨_,_,Direction.representative i,Direction.representative j,rfl⟩,rfl⟩

def Rainbow (p : Fin 3→Point) : Prop :=
  (∀r,∃F,∃hF : F≠0,InMatching r F ∧ p r=Projectivization.mk ℂ F hF) ∧
    Projectivization.IsCollinear {p 0,p 1,p 2}

theorem no_rainbow (p : Fin 3→Point) : ¬Rainbow p := by
  intro hp
  obtain ⟨F0,hF0,⟨U,V,hU,hV,rfl⟩,he0⟩ := hp.1 0
  obtain ⟨F1,hF1,⟨S,T,hS,hT,rfl⟩,he1⟩ := hp.1 1
  obtain ⟨F2,hF2,⟨M,N,hM,hN,rfl⟩,he2⟩ := hp.1 2
  have hc := hp.2
  rw [he0,he1,he2] at hc
  exact not_direction_Q2 (rainbow_forces_Q2 matrixFamily U V S T M N hU hV hS hT hM hN hc)

theorem all_rainbows_empty : {p : Fin 3→Point | Rainbow p}=∅ := by
  ext p
  simp [no_rainbow p]

theorem all_rainbows_card : {p : Fin 3→Point | Rainbow p}.ncard=0 := by
  rw [all_rainbows_empty,Set.ncard_empty]

end External
end
end Holant.Certificates.RainbowOrbit
