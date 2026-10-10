import Holant.Certificates.PlatonicIncidence.MonochromaticMarked
import Holant.Certificates.PlatonicAtlas.Incidences

/-! Exact monochromatic deck incidences at the original equal-factor point.
Both ordered factor choices are counted and proved distinct. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
attribute [local instance] Classical.propDecidable
local instance monochromaticIncidencesPointDecidable : DecidableEq Point := Classical.decEq _
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rulingsAt (r : Fin 3) (z : ι) (D : Finset (Finset ι)) : Finset (Finset (MatchingIndex ι)) :=
  (Finset.univ.product (D.filter (fun L => z∈L))).image
    (fun p : Bool × Finset ι => rulingSet r p.1 z p.2)

theorem rulingsAt_exact (r : Fin 3) (z : ι) (D : Finset (Finset ι)) :
    (monochromaticLines D).filter (fun S => (r,z,z)∈S)=rulingsAt r z D := by
  ext S
  simp only [monochromaticLines,Finset.mem_filter,Finset.mem_image,rulingsAt]
  constructor
  · rintro ⟨⟨⟨s,b,f,L⟩,hp,rfl⟩,hz⟩
    have hL : L∈D := by simpa [rulingParameters] using hp
    have hh : r=s ∧ z=f ∧ z∈L := by
      cases b <;> simpa [rulingMap] using hz
    rcases hh with ⟨hrs,hzf,hzL⟩
    subst s
    subst f
    exact ⟨(b,L),by simp [hL,hzL],rfl⟩
  · rintro ⟨⟨b,L⟩,hp,rfl⟩
    have hh : L∈D ∧ z∈L := by simpa using hp
    refine ⟨⟨(r,b,z,L),by simpa [rulingParameters] using hh.1,rfl⟩,?_⟩
    cases b <;> simp [hh.2]

theorem rulingsAt_card (r : Fin 3) (z : ι) (D : Finset (Finset ι))
    (hD : ∀L∈D,2≤L.card) :
    (rulingsAt r z D).card=2*(D.filter (fun L => z∈L)).card := by
  have hinj : Set.InjOn (fun p : Bool×Finset ι => rulingSet r p.1 z p.2)
      (((Finset.univ : Finset Bool).product (D.filter (fun L => z∈L))) : Set (Bool×Finset ι)) := by
    rintro ⟨b,L⟩ hp ⟨c,M⟩ hq he
    have hL : L∈D := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).1
    have hM : M∈D := (Finset.mem_filter.mp (Finset.mem_product.mp hq).2).1
    obtain ⟨_,hbc,_,hLM⟩ := rulingSet_injective r r b c z z L M (hD L hL) (hD M hM) he
    exact Prod.ext hbc hLM
  rw [rulingsAt,Finset.card_image_iff.mpr hinj]
  exact Finset.card_product (Finset.univ : Finset Bool) (D.filter (fun L => z∈L))

theorem monochromatic_index_incidences (r : Fin 3) (z : ι) (D : Finset (Finset ι))
    (hD : ∀L∈D,2≤L.card) (n : ℕ) :
    ((monochromaticLines D).filter (fun S => (r,z,z)∈S ∧ S.card=n)).card=
      2*(D.filter (fun L => z∈L ∧ L.card=n)).card := by
  have he : (monochromaticLines D).filter (fun S => (r,z,z)∈S ∧ S.card=n)=
      (monochromaticLines (D.filter (fun L => L.card=n))).filter (fun S => (r,z,z)∈S) := by
    rw [←monochromaticLines_filter,Finset.filter_filter]
    simp only [and_comm]
  rw [he,rulingsAt_exact,rulingsAt_card r z _ (fun L hL => hD L (Finset.mem_filter.mp hL).1),
    Finset.filter_filter]
  simp only [and_comm]

theorem actual_monochromatic_incidences (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (r : Fin 3) (z : ι) (D : Finset (Finset ι)) (hD : ∀L∈D,2≤L.card) (n : ℕ) :
    ((actualMonochromaticLines K hdet D).filter
      (fun (Q : Finset Point) => configurationPoint K hdet (r,z,z)∈Q ∧ Q.card=n)).card=
      2*(D.filter (fun L => z∈L ∧ L.card=n)).card := by
  classical
  have hm (S : Finset (MatchingIndex ι)) : configurationPoint K hdet (r,z,z)∈
      configurationPoints K hdet S ↔ (r,z,z)∈S := by
    exact Finset.mem_image.trans ⟨fun ⟨p,hp,he⟩ =>
      (configurationPoint_injective K hdet hfaith he) ▸ hp,fun hp => ⟨_,hp,rfl⟩⟩
  have he : (actualMonochromaticLines K hdet D).filter
      (fun (Q : Finset Point) => configurationPoint K hdet (r,z,z)∈Q ∧ Q.card=n)=
      ((monochromaticLines D).filter (fun S => (r,z,z)∈S ∧ S.card=n)).image
        (configurationPoints K hdet) := by
    ext Q
    simp only [actualMonochromaticLines,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨S,hS,rfl⟩,hp,hc⟩
      exact ⟨S,⟨hS,(hm S).mp hp,by simpa only [configurationPoints_card K hdet hfaith] using hc⟩,rfl⟩
    · rintro ⟨S,⟨hS,hp,hc⟩,rfl⟩
      exact ⟨⟨S,hS,rfl⟩,(hm S).mpr hp,by simpa only [configurationPoints_card K hdet hfaith] using hc⟩
  rw [he,Finset.card_image_of_injective _ (configurationPoints_injective K hdet hfaith)]
  exact monochromatic_index_incidences r z D hD n

theorem rich_domain_incidences (g : PlatonicModel) (z : Fin (size g)) (n : ℕ) (hn : 3≤n) :
    ((richDomainLines g).filter (fun L => z∈L ∧ L.card=n)).card=(linesThrough g z n).card := by
  have he : (richDomainLines g).filter (fun L => z∈L ∧ L.card=n)=
      (domainLines g).filter (fun L => z∈L ∧ L.card=n) := by
    ext L
    simp only [richDomainLines,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hD,_⟩,hz,hc⟩
      exact ⟨hD,hz,hc⟩
    · rintro ⟨hD,hz,hc⟩
      exact ⟨⟨hD,by omega⟩,hz,hc⟩
  rw [he,domainLines,Finset.filter_map,Finset.card_map]
  rfl

theorem standard_monochromatic_incidences (g : PlatonicModel) (r : Fin 3)
    (z : Fin (size g)) (n : ℕ) (hn : 3≤n) :
    ((standardMonochromaticLines g).filter
      (fun (Q : Finset Point) => deckPoint g (r,z,z)∈Q ∧ Q.card=n)).card=2*(linesThrough g z n).card := by
  exact (actual_monochromatic_incidences (representative g) (representative_det_ne_zero g)
    (representative_proportional_faithful g) r z (richDomainLines g)
    (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2) n).trans
      (congrArg (fun c => 2*c) (rich_domain_incidences g z n hn))

 theorem external_monochromatic_incidences (r : Fin 3) (z : Fin 12) :
    ((externalMonochromaticLines).filter
      (fun (Q : Finset Point) => External.deckPoint (r,z,z)∈Q ∧ Q.card=3)).card=8 := by
  exact (actual_monochromatic_incidences External.representative External.representative_det_ne_zero
    external_representative_faithful r z (richDomainLines .tetrahedral)
    (fun L hL => le_trans (by decide : 2≤3) (Finset.mem_filter.mp hL).2) 3).trans
      ((congrArg (fun c => 2*c) (rich_domain_incidences .tetrahedral z 3 (by decide))).trans
        (congrArg (fun c => 2*c) (tetrahedral_point_incidences z)))

end
end Holant.Certificates.PlatonicAtlas
