import Holant.Certificates.PlatonicIncidence.MonochromaticClassification

/-! The ruling certificates describe every rich intersection with an arbitrary
actual two-dimensional complex coefficient subspace, as projective point sets. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def configurationPoint (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (p : MatchingIndex ι) : Point :=
  Projectivization.mk ℂ (configurationTensor K p) (configurationTensor_nonzero K hdet p)

def configurationPoints (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (S : Finset (MatchingIndex ι)) : Finset Point := by
  classical
  exact S.image (configurationPoint K hdet)

theorem configurationPoint_injective (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j) :
    Function.Injective (configurationPoint K hdet) := by
  intro p q he
  exact (configurationTensor_proportional_iff K hdet hfaith p q).mp
    ((proportional_point_iff _ _ _ _).mpr he)

theorem configurationPoints_injective (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j) :
    Function.Injective (configurationPoints K hdet) := by
  classical
  exact Finset.image_injective (configurationPoint_injective K hdet hfaith)

@[simp] theorem configurationPoints_card (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀ i j,Proportional (K i) (K j)→i=j) (S : Finset (MatchingIndex ι)) :
    (configurationPoints K hdet S).card=S.card := by
  classical
  exact Finset.card_image_of_injective _ (configurationPoint_injective K hdet hfaith)

/-- All deck representatives in an arbitrary complex coefficient subspace. -/
def configurationIntersection (K : ι → BinaryMatrix) (W : Submodule ℂ FourTensor) :
    Finset (MatchingIndex ι) := by
  classical
  exact Finset.univ.filter (fun p => configurationTensor K p∈W)

@[simp] theorem mem_configurationIntersection (K : ι → BinaryMatrix)
    (W : Submodule ℂ FourTensor) (p : MatchingIndex ι) :
    p∈configurationIntersection K W ↔ configurationTensor K p∈W := by
  classical
  simp [configurationIntersection]

theorem configuration_subspace_eq_pair (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (W : Submodule ℂ FourTensor) (hW : Module.finrank ℂ W≤2)
    (p q : MatchingIndex ι) (hpq : p≠q)
    (hp : configurationTensor K p∈W) (hq : configurationTensor K q∈W) :
    W=Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor) := by
  have hle : Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor)≤W := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl|hv
    · exact hp
    · rcases hv with rfl
      exact hq
  exact (Submodule.eq_of_le_of_finrank_le hle (by
    rw [configuration_pair_finrank K hdet hfaith p q hpq]
    exact hW)).symm

/-- No arbitrary complex line is omitted by the finite secant representation. -/
theorem configurationIntersection_secant (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (W : Submodule ℂ FourTensor) (hW : Module.finrank ℂ W≤2)
    (hcard : 2≤(configurationIntersection K W).card) :
    MatchingSecant K (configurationIntersection K W) := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1<(configurationIntersection K W).card)
  have he := configuration_subspace_eq_pair K hdet hfaith W hW p q hpq
    ((mem_configurationIntersection K W p).mp hp) ((mem_configurationIntersection K W q).mp hq)
  exact ⟨p,q,hpq,by intro x; rw [mem_configurationIntersection,he]⟩

/-- A maximal rich actual projective deck line: its points are the entire
intersection of the deck with an arbitrary complex projective line. -/
def ActualRichLine (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0) (Q : Finset Point) : Prop :=
  ∃ W : Submodule ℂ FourTensor,Module.finrank ℂ W=2 ∧
    Q=configurationPoints K hdet (configurationIntersection K W) ∧ 3≤Q.card

theorem actualRichLine_iff (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (Q : Finset Point) :
    ActualRichLine K hdet Q ↔
      ∃S : Finset (MatchingIndex ι),MatchingSecant K S ∧ 3≤S.card ∧ Q=configurationPoints K hdet S := by
  constructor
  · rintro ⟨W,hW,rfl,hcard⟩
    have hc : 3≤(configurationIntersection K W).card := by
      simpa only [configurationPoints_card K hdet hfaith] using hcard
    exact ⟨_,configurationIntersection_secant K hdet hfaith W hW.le (by omega),hc,rfl⟩
  · rintro ⟨S,⟨p,q,hpq,hS⟩,hc,rfl⟩
    let W := Submodule.span ℂ ({configurationTensor K p,configurationTensor K q} : Set FourTensor)
    have hEq : S=configurationIntersection K W := by
      ext x
      exact (hS x).trans (mem_configurationIntersection K W x).symm
    refine ⟨W,configuration_pair_finrank K hdet hfaith p q hpq,?_,?_⟩
    · rw [hEq]
    · simpa only [configurationPoints_card K hdet hfaith] using hc

/-- Source-level completeness for arbitrary actual complex projective lines. -/
theorem actualRichLine_classification (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (Q : Finset Point) (hQ : ActualRichLine K hdet Q) :
    (∃ r b f L,BinarySecant K L ∧ 3≤L.card ∧ Q=configurationPoints K hdet (rulingSet r b f L)) ∨
      (Q.card=3 ∧ ∃S : Finset (MatchingIndex ι),Q=configurationPoints K hdet S ∧
        ∀r : Fin 3,∃!p,p∈S ∧ p.1=r) := by
  obtain ⟨S,hS,hc,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp hQ
  rcases matchingSecant_classification K hdet hfaith S hS hc with h|h
  · obtain ⟨r,b,f,L,hL,hcL,rfl⟩ := h
    exact Or.inl ⟨r,b,f,L,hL,hcL,rfl⟩
  · exact Or.inr ⟨by simpa only [configurationPoints_card K hdet hfaith] using h.1,S,rfl,h.2⟩

def actualMonochromaticLines (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (D : Finset (Finset ι)) : Finset (Finset Point) := by
  classical
  exact (monochromaticLines D).image (configurationPoints K hdet)

/-- Counts refer to distinct sets of actual complex projective deck points. -/
theorem actualMonochromaticLines_filter_card (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (D : Finset (Finset ι)) (hD : ∀L∈D,2≤L.card) (n : ℕ) :
    ((actualMonochromaticLines K hdet D).filter (fun Q => Q.card=n)).card=
      6*Fintype.card ι*(D.filter (fun L => L.card=n)).card := by
  classical
  have he : (actualMonochromaticLines K hdet D).filter (fun Q => Q.card=n)=
      ((monochromaticLines D).filter (fun S => S.card=n)).image (configurationPoints K hdet) := by
    ext Q
    simp only [actualMonochromaticLines,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨S,hS,rfl⟩,hc⟩
      exact ⟨S,⟨hS,by simpa only [configurationPoints_card K hdet hfaith] using hc⟩,rfl⟩
    · rintro ⟨S,⟨hS,hc⟩,rfl⟩
      exact ⟨⟨S,hS,rfl⟩,by simpa only [configurationPoints_card K hdet hfaith] using hc⟩
  rw [he,Finset.card_image_of_injective _ (configurationPoints_injective K hdet hfaith)]
  exact monochromaticLines_filter_card D hD n

/-- One matching label on an actual projective point set. -/
def ActualOneMatching (K : ι → BinaryMatrix) (hdet : ∀i,(K i).det≠0) (Q : Finset Point) : Prop :=
  ∃r : Fin 3,∀p,configurationPoint K hdet p∈Q→p.1=r

theorem actualMonochromaticLines_exact (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (D : Finset (Finset ι))
    (hD : ∀L,L∈D ↔ BinarySecant K L ∧ 3≤L.card) (Q : Finset Point) :
    Q∈actualMonochromaticLines K hdet D ↔ ActualRichLine K hdet Q ∧ ActualOneMatching K hdet Q := by
  classical
  have hm (S : Finset (MatchingIndex ι)) (p : MatchingIndex ι) :
      configurationPoint K hdet p∈configurationPoints K hdet S ↔ p∈S :=
    Finset.mem_image.trans ⟨by
      rintro ⟨q,hq,he⟩
      exact configurationPoint_injective K hdet hfaith he ▸ hq,
      by intro hp; exact ⟨p,hp,rfl⟩⟩
  constructor
  · intro h
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hs,hc,r,hr⟩ := (monochromaticLines_exact K hdet hfaith D hD S).mp hS
    refine ⟨(actualRichLine_iff K hdet hfaith _).mpr ⟨S,hs,hc,rfl⟩,r,?_⟩
    exact fun p hp => hr p ((hm S p).mp hp)
  · rintro ⟨hQ,r,hr⟩
    obtain ⟨S,hS,hc,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp hQ
    apply Finset.mem_image.mpr
    refine ⟨S,(monochromaticLines_exact K hdet hfaith D hD S).mpr ⟨hS,hc,r,?_⟩,rfl⟩
    exact fun p hp => hr p ((hm S p).mpr hp)

end
end Holant.Certificates.PlatonicIncidence
