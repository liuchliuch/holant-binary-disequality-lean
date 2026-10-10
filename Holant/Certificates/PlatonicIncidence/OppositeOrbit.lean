import Holant.Certificates.PlatonicIncidence.OppositeDeck

namespace Holant.Certificates.PlatonicIncidence.Opposite
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OppositeIcosahedral
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def Rainbow (p : Fin 3→Point) : Prop := FamilyRainbow Direction p

def orbitPoint (t : OrbitIndex .icosahedral) : Fin 3→Point :=
  fun r => point (RainbowOrbit.orbitPoint .icosahedral t r)

theorem orbitPoint_injective : Function.Injective orbitPoint := by
  intro t s h
  apply RainbowOrbit.orbitPoint_injective .icosahedral
  funext r
  exact point_injective (congrFun h r)

theorem rainbow_forward (p : Fin 3→Point) (hp : RainbowOrbit.Rainbow .icosahedral p) :
    Rainbow (fun r => point (p r)) := by
  constructor
  · intro r
    obtain ⟨F,hF,hM,he⟩ := hp.1 r
    refine ⟨act legs F,act_nonzero _ legs_det hF,matching_forward r F hM,?_⟩
    change point (p r)=_
    rw [he]
    rfl
  · have hh := pointAction_collinear legs legs_det _ hp.2
    simpa only [point,Set.image_insert_eq,Set.image_singleton] using hh

theorem rainbow_enumerated (p : Fin 3→Point) (hp : Rainbow p) :
    ∃t : OrbitIndex .icosahedral,p=orbitPoint t := by
  choose F hF hM he using hp.1
  have hh : ∀r,∃H,RainbowOrbit.InMatching .icosahedral r H ∧ act legs H=F r :=
    fun r => matching_surjective r (F r) (hM r)
  choose H hH hHE using hh
  have hH0 (r : Fin 3) : H r≠0 := by
    intro hz
    apply hF r
    rw [←hHE r,hz]
    simp [act]
  let q : Fin 3→Point := fun r => Projectivization.mk ℂ (H r) (hH0 r)
  have hpq (r : Fin 3) : p r=point (q r) := by
    rw [he r]
    change Projectivization.mk ℂ (F r) _=Projectivization.mk ℂ (act legs (H r)) _
    congr 1
    exact (hHE r).symm
  have hq : RainbowOrbit.Rainbow .icosahedral q := by
    constructor
    · exact fun r => ⟨H r,hH0 r,hH r,rfl⟩
    · have hc := hp.2
      rw [hpq 0,hpq 1,hpq 2] at hc
      apply (pointAction_collinear_iff legs legs_det {q 0,q 1,q 2}).mp
      simpa only [point,Set.image_insert_eq,Set.image_singleton] using hc
  obtain ⟨t,ht⟩ := RainbowOrbit.rainbow_enumerated .icosahedral q hq
  refine ⟨t,?_⟩
  funext r
  rw [hpq r,ht]
  rfl

def line (t : OrbitIndex .icosahedral) : Finset Point := points (orbitPoint t)

theorem line_eq_map (t : OrbitIndex .icosahedral) :
    line t=(RainbowOrbit.line .icosahedral t).map ⟨point,point_injective⟩ := by
  classical
  ext p
  simp [line,RainbowOrbit.line,points,orbitPoint]

theorem line_injective : Function.Injective line := by
  intro t s he
  simp only [line_eq_map] at he
  exact RainbowOrbit.line_injective .icosahedral (Finset.map_injective _ he)

def lines : Finset (Finset Point) := by
  classical
  exact Finset.univ.map ⟨line,line_injective⟩

def RainbowLine (S : Finset Point) : Prop := FamilyRainbowLine Direction S

theorem rainbowLine_iff_mem (S : Finset Point) : RainbowLine S ↔ S∈lines := by
  classical
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨t,rfl⟩ := rainbow_enumerated p hp
    exact Finset.mem_map.mpr ⟨t,Finset.mem_univ _,rfl⟩
  · intro hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨_,rainbow_forward _ (orbitPoint_rainbow .icosahedral t),rfl⟩

theorem lines_card : lines.card=216000 := by
  simp [lines,OrbitIndex,size]

theorem all_rainbow_lines_card : {S : Finset Point | RainbowLine S}.ncard=216000 := by
  classical
  have he : {S : Finset Point | RainbowLine S}=(lines : Set (Finset Point)) := by
    ext S
    exact rainbowLine_iff_mem S
  rw [he,Set.ncard_coe_finset,lines_card]

theorem line_maximal {S : Finset Point} (hS : RainbowLine S) (p : Point)
    (hp : p∈deck) (hcol : Projectivization.IsCollinear (insert p (S : Set Point))) : p∈S :=
  FamilyRainbowLine.maximal (fun {U} h => Direction.det_ne_zero h) hS p
    ((deck_iff_mem p).mpr hp) hcol

end
end Holant.Certificates.PlatonicIncidence.Opposite
