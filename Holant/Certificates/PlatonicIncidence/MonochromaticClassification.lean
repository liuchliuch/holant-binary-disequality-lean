import Holant.Certificates.PlatonicIncidence.MonochromaticGeometry

namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem configuration_pair_finrank (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (p q : MatchingIndex ι) (hpq : p≠q) :
    Module.finrank ℂ (Submodule.span ℂ
      ({configurationTensor K p,configurationTensor K q} : Set FourTensor))=2 := by
  have hp := configurationTensor_nonzero K hdet p
  have hq := configurationTensor_nonzero K hdet q
  have hne : Projectivization.mk ℂ (configurationTensor K p) hp≠
      Projectivization.mk ℂ (configurationTensor K q) hq := by
    intro he
    exact hpq ((configurationTensor_proportional_iff K hdet hfaith p q).mp
      ((proportional_point_iff _ _ hp hq).mpr he))
  have hli : LinearIndependent ℂ ![configurationTensor K p,configurationTensor K q] :=
    (Projectivization.independent_mk_iff_LinearIndependent hp hq).mp
      ((Projectivization.independent_pair_iff_ne _ _).mpr hne)
  rw [←Matrix.range_cons_cons_empty _ _ ![]]
  simpa using finrank_span_eq_card hli

/-- Any two distinct deck points on a complete complex secant are valid
endpoints for that same complete secant. -/
theorem matchingSecant_rebase (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S)
    (p q : MatchingIndex ι) (hp : p∈S) (hq : q∈S) (hpq : p≠q) :
    ∀x,x∈S ↔ configurationTensor K x∈Submodule.span ℂ
      ({configurationTensor K p,configurationTensor K q} : Set FourTensor) := by
  obtain ⟨u,v,huv,hspan⟩ := hS
  have hle : Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor)≤
      Submodule.span ℂ ({configurationTensor K u,configurationTensor K v} : Set FourTensor) := by
    apply Submodule.span_le.mpr
    intro t ht
    rcases ht with rfl|ht
    · exact (hspan p).mp hp
    · rcases ht with rfl
      exact (hspan q).mp hq
  have he := Submodule.eq_of_le_of_finrank_le hle (by
    rw [configuration_pair_finrank K hdet hfaith p q hpq,
      configuration_pair_finrank K hdet hfaith u v huv])
  intro x
  rw [he]
  exact hspan x

/-- Repeating a matching label on a secant excludes both other labels. -/
theorem matchingSecant_repeated_label (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S)
    (p q : MatchingIndex ι) (hp : p∈S) (hq : q∈S) (hpq : p≠q) (hlabel : p.1=q.1) :
    ∀x∈S,x.1=p.1 := by
  have hspan := matchingSecant_rebase K hdet hfaith S hS p q hp hq hpq
  rcases p with ⟨r,i,j⟩
  rcases q with ⟨s,k,l⟩
  change r=s at hlabel
  subst s
  rintro ⟨s,m,n⟩ hw
  change s=r
  by_contra hsr
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp ((hspan _).mp hw)
  exact no_mixed_matching_line r s (Ne.symm hsr) (K i) (K j) (K k) (K l) (K m) (K n)
    (hdet i) (hdet j) (hdet k) (hdet l) (hdet m) (hdet n) a b he

/-- A rich line is either one complete Segre ruling or exactly three points,
one of each matching label. This simultaneously excludes type (2,1) and all
larger mixed lines. -/
theorem matchingSecant_classification (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S) (hrich : 3≤S.card) :
    (∃ r b f L,BinarySecant K L ∧ 3≤L.card ∧ S=rulingSet r b f L) ∨
      (S.card=3 ∧ ∀r : Fin 3,∃!p,p∈S ∧ p.1=r) := by
  classical
  by_cases hone : HasOneMatching S
  · exact Or.inl (monochromatic_secant_ruling K hdet hfaith S hS hrich hone)
  · right
    have hinj : Set.InjOn (fun p : MatchingIndex ι => p.1) S := by
      intro p hp q hq hlabel
      by_contra hpq
      exact hone ⟨p.1,matchingSecant_repeated_label K hdet hfaith S hS p q hp hq hpq hlabel⟩
    have hcimage : (S.image (fun p => p.1)).card=S.card := Finset.card_image_iff.mpr hinj
    have hc : S.card=3 := by
      have hle : (S.image (fun p => p.1)).card≤3 := by
        simpa using Finset.card_le_card (Finset.subset_univ (S.image (fun p => p.1)))
      omega
    have hlabels : S.image (fun p => p.1)=Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa [hcimage,hc]
    refine ⟨hc,?_⟩
    intro r
    have hr : r∈S.image (fun p => p.1) := by rw [hlabels]; exact Finset.mem_univ _
    obtain ⟨p,hp,hpr⟩ := Finset.mem_image.mp hr
    refine ⟨p,⟨hp,hpr⟩,?_⟩
    intro q hq
    exact hinj hq.1 hp (hq.2.trans hpr.symm)

/-- No mixed deck secant can have four or more points. -/
theorem matchingSecant_large_monochromatic (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (hS : MatchingSecant K S) (hlarge : 4≤S.card) :
    HasOneMatching S := by
  rcases matchingSecant_classification K hdet hfaith S hS (by omega) with h|h
  · obtain ⟨r,b,f,L,_,_,rfl⟩ := h
    exact ⟨r,fun p hp => (mem_rulingSet r b f L p).mp hp |>.1⟩
  · omega

end
end Holant.Certificates.PlatonicIncidence
