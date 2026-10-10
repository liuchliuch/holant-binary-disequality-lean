import Holant.Certificates.RainbowOrbit.Orbit

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem rainbow_enumerated (g : PlatonicModel) (p : Fin 3→Point) (hp : Rainbow g p) :
    ∃t : OrbitIndex g,p=orbitPoint g t := by
  obtain ⟨F0,hF0,⟨U,V,hU,hV,rfl⟩,he0⟩ := hp.1 0
  obtain ⟨F1,hF1,⟨S,T,hS,hT,rfl⟩,he1⟩ := hp.1 1
  obtain ⟨F2,hF2,⟨M,N,hM,hN,rfl⟩,he2⟩ := hp.1 2
  have hdu := groupDirection_det_ne_zero g hU
  have hdv := groupDirection_det_ne_zero g hV
  have hds := groupDirection_det_ne_zero g hS
  have hdt := groupDirection_det_ne_zero g hT
  have hdm := groupDirection_det_ne_zero g hM
  have hdn := groupDirection_det_ne_zero g hN
  have hcol := hp.2
  rw [he0,he1,he2] at hcol
  have hn01 : ¬Proportional (matchingTensor 0 U V) (matchingTensor 1 S T) := by
    intro h
    have hh := proportional_matching_labels 0 1 U V S T hdu hdv hds hdt h
    exact (by decide : (0 : Fin 3)≠1) hh
  have hn20 : ¬Proportional (matchingTensor 2 M N) (matchingTensor 0 U V) := by
    intro h
    have hh := proportional_matching_labels 2 0 M N U V hdm hdn hdu hdv h
    exact (by decide : (2 : Fin 3)≠0) hh
  have hn21 : ¬Proportional (matchingTensor 2 M N) (matchingTensor 1 S T) := by
    intro h
    have hh := proportional_matching_labels 2 1 M N S T hdm hdn hds hdt h
    exact (by decide : (2 : Fin 3)≠1) hh
  obtain ⟨α,β,hα,hβ,hline⟩ := (collinear_triple_iff _ _ _ hF0 hF1 hF2 hn01 hn20 hn21).mp hcol
  obtain ⟨h0,h1,h2⟩ := normalize_rainbow U V S T M N hdu hdv hds hdm hdn α β hα hβ hline
  let L := normalization U V S
  have hL : GroupLegs g L := normalization_mem g U V S hU hV hS
  let L' : Legs := fun j => (L j)⁻¹
  have hL' : GroupLegs g L' := hL.inverse
  obtain ⟨t,ht⟩ := group_action_enumerated g L' hL'
  refine ⟨t,?_⟩
  have hi (F H : FourTensor) (h : Proportional (act L F) H) : Proportional F (act L' H) := by
    have hh := h.act L'
    simpa only [L',act_inverse L hL.det] using hh
  have hp0 : Proportional (P0 U V) (act L' A) := hi _ _ ⟨1,one_ne_zero,by simpa using h0⟩
  have hp1 : Proportional (P1 S T) (act L' B) := hi _ _ ⟨-α/β,div_ne_zero (neg_ne_zero.mpr hα) hβ,h1⟩
  have hp2 : Proportional (P2 M N) (act L' C) := hi _ _ ⟨α,hα,h2⟩
  funext r
  fin_cases r
  · change p 0=orbitPoint g t 0
    rw [he0]
    exact (proportional_point_iff _ _ _ _).mp (hp0.trans (ht 0))
  · change p 1=orbitPoint g t 1
    rw [he1]
    exact (proportional_point_iff _ _ _ _).mp (hp1.trans (ht 1))
  · change p 2=orbitPoint g t 2
    rw [he2]
    exact (proportional_point_iff _ _ _ _).mp (hp2.trans (ht 2))

theorem rainbow_iff_mem (g : PlatonicModel) (p : Fin 3→Point) :
    Rainbow g p ↔ p∈rainbowOrbit g := by
  classical
  constructor
  · intro hp
    obtain ⟨t,rfl⟩ := rainbow_enumerated g p hp
    exact Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩
  · intro hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hp
    exact orbitPoint_rainbow g t

/-- The complete actual rainbow set has |G|³ elements, not merely an orbit subset. -/
theorem all_rainbows_card (g : PlatonicModel) : {p : Fin 3→Point | Rainbow g p}.ncard=(size g)^3 := by
  classical
  have he : {p : Fin 3→Point | Rainbow g p}=(rainbowOrbit g : Set (Fin 3→Point)) := by
    ext p
    exact rainbow_iff_mem g p
  rw [he,Set.ncard_coe_finset,rainbowOrbit_card]

end
end Holant.Certificates.RainbowOrbit
