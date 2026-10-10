import Holant.Certificates.RainbowOrbit.Stabilizer
import Holant.Certificates.RainbowOrbit.GroupRepresentatives
import Mathlib.Data.Set.Card

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Point := Projectivization ℂ FourTensor
abbrev DeckIndex (g : PlatonicModel) := Fin 3 × Fin (size g) × Fin (size g)

def deckPoint (g : PlatonicModel) (i : DeckIndex g) : Point :=
  Projectivization.mk ℂ (matchingTensor i.1 (representative g i.2.1) (representative g i.2.2))
    (matching_nonzero _ _ _ (representative_det_ne_zero g _) (representative_det_ne_zero g _))

theorem deckPoint_injective (g : PlatonicModel) : Function.Injective (deckPoint g) := by
  rintro ⟨r,i,j⟩ ⟨s,k,l⟩ he
  have hp := (proportional_point_iff _ _ _ _).mpr he
  have hrs := proportional_matching_labels r s _ _ _ _
    (representative_det_ne_zero g _) (representative_det_ne_zero g _)
    (representative_det_ne_zero g _) (representative_det_ne_zero g _) hp
  subst s
  obtain ⟨⟨c,hc,hi⟩,⟨d,hd,hj⟩⟩ := proportional_matching_factors r _ _ _ _
    (representative_det_ne_zero g _) (representative_det_ne_zero g _) hp
  have hik := projectively_injective g i k c hi
  have hjl := projectively_injective g j l d hj
  subst k; subst l
  rfl

def deck (g : PlatonicModel) : Finset Point := by
  classical
  exact Finset.univ.map ⟨deckPoint g,deckPoint_injective g⟩

theorem deck_card (g : PlatonicModel) : (deck g).card=3*(size g)^2 := by
  classical
  simp [deck,DeckIndex,pow_two,Nat.mul_assoc]

def InDeck (g : PlatonicModel) (F : FourTensor) : Prop :=
  ∃ r U V, groupDirection g U ∧ groupDirection g V ∧ Proportional F (matchingTensor r U V)

theorem matching_proportional (r : Fin 3) {U V U' V' : BinaryMatrix}
    (hU : Proportional U U') (hV : Proportional V V') :
    Proportional (matchingTensor r U V) (matchingTensor r U' V') := by
  obtain ⟨c,hc,rfl⟩ := hU
  obtain ⟨d,hd,rfl⟩ := hV
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  fin_cases r <;> funext x <;> simp [matchingTensor,P0,P1,P2,Matrix.smul_apply,smul_eq_mul] <;> ring

theorem inDeck_iff_mem (g : PlatonicModel) (F : FourTensor) (hF : F≠0) :
    InDeck g F ↔ Projectivization.mk ℂ F hF ∈ deck g := by
  classical
  constructor
  · rintro ⟨r,U,V,hU,hV,hp⟩
    obtain ⟨i,c,hc,hi⟩ := (complete g U).mp hU
    obtain ⟨j,d,hd,hj⟩ := (complete g V).mp hV
    have hh := hp.trans (matching_proportional r ⟨c,hc,hi⟩ ⟨d,hd,hj⟩)
    have he := (proportional_point_iff _ _ hF (matching_nonzero r _ _
      (representative_det_ne_zero g i) (representative_det_ne_zero g j))).mp hh
    change Projectivization.mk ℂ F hF=deckPoint g (r,i,j) at he
    rw [he]
    exact Finset.mem_map.mpr ⟨(r,i,j),Finset.mem_univ _,rfl⟩
  · intro hm
    obtain ⟨⟨r,i,j⟩,_,he⟩ := Finset.mem_map.mp hm
    refine ⟨r,representative g i,representative g j,representative_mem g i,
      representative_mem g j,?_⟩
    exact (proportional_point_iff _ _ _ _).mpr he.symm

theorem standard_deck_counts : (deck .tetrahedral).card=432 ∧
    (deck .octahedral).card=1728 ∧ (deck .icosahedral).card=10800 := by
  simp [deck_card,size]

end
end Holant.Certificates.RainbowOrbit
