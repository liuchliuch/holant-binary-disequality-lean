import Holant.Certificates.RainbowOrbit.OrbitCompleteness

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem InMatching.point_labels {g : PlatonicModel} {r s : Fin 3} {F H : FourTensor}
    (hF : InMatching g r F) (hH : InMatching g s H) (h : Proportional F H) : r=s := by
  obtain ⟨U,V,hU,hV,rfl⟩ := hF
  obtain ⟨S,T,hS,hT,rfl⟩ := hH
  exact proportional_matching_labels r s U V S T (groupDirection_det_ne_zero g hU)
    (groupDirection_det_ne_zero g hV) (groupDirection_det_ne_zero g hS) (groupDirection_det_ne_zero g hT) h

theorem Rainbow.point_labels {g : PlatonicModel} {p q : Fin 3→Point}
    (hp : Rainbow g p) (hq : Rainbow g q) (r s : Fin 3) (he : p r=q s) : r=s := by
  obtain ⟨F,hF,hr,heF⟩ := hp.1 r
  obtain ⟨H,hH,hs,heH⟩ := hq.1 s
  rw [heF,heH] at he
  exact hr.point_labels hs ((proportional_point_iff F H hF hH).mpr he)

def points (p : Fin 3→Point) : Finset Point := by
  classical
  exact Finset.univ.image p

theorem points_card {g : PlatonicModel} {p : Fin 3→Point} (hp : Rainbow g p) : (points p).card=3 := by
  classical
  have hi : Function.Injective p := fun r s he => hp.point_labels hp r s he
  simp [points,Finset.card_image_of_injective _ hi]

theorem points_injective {g : PlatonicModel} {p q : Fin 3→Point}
    (hp : Rainbow g p) (hq : Rainbow g q) (he : points p=points q) : p=q := by
  classical
  funext r
  have hm : p r∈points q := by rw [←he]; exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hm
  have hrs := hp.point_labels hq r s hs.symm
  simpa [hrs] using hs.symm

def line (g : PlatonicModel) (t : OrbitIndex g) : Finset Point := points (orbitPoint g t)

theorem line_injective (g : PlatonicModel) : Function.Injective (line g) := by
  intro t s he
  exact orbitPoint_injective g (points_injective (orbitPoint_rainbow g t) (orbitPoint_rainbow g s) he)

def lines (g : PlatonicModel) : Finset (Finset Point) := by
  classical
  exact Finset.univ.map ⟨line g,line_injective g⟩

/-- The unordered three-point subset is the geometric object being counted. -/
def RainbowLine (g : PlatonicModel) (S : Finset Point) : Prop :=
  ∃p : Fin 3→Point, Rainbow g p ∧ S=points p

theorem rainbowLine_iff_mem (g : PlatonicModel) (S : Finset Point) :
    RainbowLine g S ↔ S∈lines g := by
  classical
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,rfl⟩ := rainbow_enumerated g p hp
    exact Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩
  · intro hm
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hm
    exact ⟨_,orbitPoint_rainbow g t,rfl⟩

theorem lines_card (g : PlatonicModel) : (lines g).card=(size g)^3 := by
  classical
  simp [lines,OrbitIndex]

theorem all_rainbow_lines_card (g : PlatonicModel) :
    {S : Finset Point | RainbowLine g S}.ncard=(size g)^3 := by
  classical
  have he : {S : Finset Point | RainbowLine g S}=(lines g : Set (Finset Point)) := by
    ext S
    exact rainbowLine_iff_mem g S
  rw [he,Set.ncard_coe_finset,lines_card]

theorem rainbowLine_three {g : PlatonicModel} {S : Finset Point} (hS : RainbowLine g S) : S.card=3 := by
  obtain ⟨p,hp,rfl⟩ := hS
  exact points_card hp

end
end Holant.Certificates.RainbowOrbit
