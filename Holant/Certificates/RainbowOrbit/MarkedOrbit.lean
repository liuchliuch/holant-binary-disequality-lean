import Holant.Certificates.RainbowOrbit.MarkedDeck

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

def markPoint (f : Form) : Point→Point := pointAction (markLegs f) (markLegs_det f)

theorem markPoint_injective (f : Form) : Function.Injective (markPoint f) := pointAction_injective _ _

def markedOrbitPoint (f : Form) (t : OrbitIndex .octahedral) : Fin 3→Point :=
  fun r => markPoint f (orbitPoint .octahedral t r)

theorem markedOrbitPoint_injective (f : Form) : Function.Injective (markedOrbitPoint f) := by
  intro t s he
  apply orbitPoint_injective .octahedral
  funext r
  exact markPoint_injective f (congrFun he r)

def markedRainbowOrbit (f : Form) : Finset (Fin 3→Point) := by
  classical
  exact Finset.univ.map ⟨markedOrbitPoint f,markedOrbitPoint_injective f⟩

def MarkedRainbow (f : Form) (p : Fin 3→Point) : Prop :=
  (∀r,∃F,∃hF : F≠0,MarkedInMatching f r F ∧ p r=Projectivization.mk ℂ F hF) ∧
    Projectivization.IsCollinear {p 0,p 1,p 2}

theorem rainbow_mark_forward (f : Form) (p : Fin 3→Point) (hp : Rainbow .octahedral p) :
    MarkedRainbow f (fun r => markPoint f (p r)) := by
  constructor
  · intro r
    obtain ⟨F,hF,hM,he⟩ := hp.1 r
    refine ⟨act (markLegs f) F,act_nonzero _ (markLegs_det f) hF,
      matching_mark_forward f r F hM,?_⟩
    change markPoint f (p r)=_
    rw [he]
    rfl
  · have hh := pointAction_collinear (markLegs f) (markLegs_det f) _ hp.2
    simpa only [markPoint,Set.image_insert_eq,Set.image_singleton] using hh

theorem marked_rainbow_enumerated (f : Form) (p : Fin 3→Point) (hp : MarkedRainbow f p) :
    ∃t : OrbitIndex .octahedral,p=markedOrbitPoint f t := by
  choose F hF hM he using hp.1
  have hh : ∀r,∃H,InMatching .octahedral r H ∧ act (markLegs f) H=F r :=
    fun r => matching_mark_surjective f r (F r) (hM r)
  choose H hH hHE using hh
  have hH0 (r : Fin 3) : H r≠0 := by
    intro hz
    apply hF r
    rw [←hHE r,hz]
    simp [act]
  let q : Fin 3→Point := fun r => Projectivization.mk ℂ (H r) (hH0 r)
  have hpq (r : Fin 3) : p r=markPoint f (q r) := by
    rw [he r]
    change Projectivization.mk ℂ (F r) _=Projectivization.mk ℂ (act (markLegs f) (H r)) _
    congr 1
    exact (hHE r).symm
  have hq : Rainbow .octahedral q := by
    constructor
    · exact fun r => ⟨H r,hH0 r,hH r,rfl⟩
    · have hc := hp.2
      rw [hpq 0,hpq 1,hpq 2] at hc
      apply (pointAction_collinear_iff (markLegs f) (markLegs_det f) {q 0,q 1,q 2}).mp
      simpa only [markPoint,Set.image_insert_eq,Set.image_singleton] using hc
  obtain ⟨t,ht⟩ := rainbow_enumerated .octahedral q hq
  refine ⟨t,?_⟩
  funext r
  rw [hpq r,ht]
  rfl

theorem marked_rainbow_iff_mem (f : Form) (p : Fin 3→Point) :
    MarkedRainbow f p ↔ p∈markedRainbowOrbit f := by
  classical
  constructor
  · intro hp
    obtain ⟨t,rfl⟩ := marked_rainbow_enumerated f p hp
    exact Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩
  · intro hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hp
    exact rainbow_mark_forward f _ (orbitPoint_rainbow .octahedral t)

theorem markedRainbowOrbit_card (f : Form) : (markedRainbowOrbit f).card=13824 := by
  simp [markedRainbowOrbit,OrbitIndex,size]

theorem marked_all_rainbows_card (f : Form) : {p : Fin 3→Point | MarkedRainbow f p}.ncard=13824 := by
  classical
  have he : {p : Fin 3→Point | MarkedRainbow f p}=(markedRainbowOrbit f : Set (Fin 3→Point)) := by
    ext p
    exact marked_rainbow_iff_mem f p
  rw [he,Set.ncard_coe_finset,markedRainbowOrbit_card]

def markedLine (f : Form) (t : OrbitIndex .octahedral) : Finset Point := points (markedOrbitPoint f t)

theorem markedLine_eq_map (f : Form) (t : OrbitIndex .octahedral) :
    markedLine f t=(line .octahedral t).map ⟨markPoint f,markPoint_injective f⟩ := by
  classical
  ext p
  simp [markedLine,line,points,markedOrbitPoint]

theorem markedLine_injective (f : Form) : Function.Injective (markedLine f) := by
  intro t s he
  simp only [markedLine_eq_map] at he
  exact line_injective .octahedral (Finset.map_injective _ he)

def markedLines (f : Form) : Finset (Finset Point) := by
  classical
  exact Finset.univ.map ⟨markedLine f,markedLine_injective f⟩

def MarkedRainbowLine (f : Form) (S : Finset Point) : Prop :=
  ∃p : Fin 3→Point,MarkedRainbow f p ∧ S=points p

theorem marked_rainbowLine_iff_mem (f : Form) (S : Finset Point) :
    MarkedRainbowLine f S ↔ S∈markedLines f := by
  classical
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,rfl⟩ := marked_rainbow_enumerated f p hp
    exact Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩
  · intro hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨_,rainbow_mark_forward f _ (orbitPoint_rainbow .octahedral t),rfl⟩

theorem markedLines_card (f : Form) : (markedLines f).card=13824 := by
  simp [markedLines,OrbitIndex,size]

theorem marked_all_lines_card (f : Form) : {S : Finset Point | MarkedRainbowLine f S}.ncard=13824 := by
  classical
  have he : {S : Finset Point | MarkedRainbowLine f S}=(markedLines f : Set (Finset Point)) := by
    ext S
    exact marked_rainbowLine_iff_mem f S
  rw [he,Set.ncard_coe_finset,markedLines_card]

end
end Holant.Certificates.RainbowOrbit
