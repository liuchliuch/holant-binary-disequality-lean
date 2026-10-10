import Holant.Certificates.PlatonicIncidence.MonochromaticCompletion

namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mem_configurationPoints (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (S : Finset (MatchingIndex ι)) (p : MatchingIndex ι) :
    configurationPoint K hdet p∈configurationPoints K hdet S ↔ p∈S := by
  classical
  exact Finset.mem_image.trans ⟨by
    rintro ⟨q,hq,he⟩
    exact configurationPoint_injective K hdet hfaith he ▸ hq,
    by intro hp; exact ⟨p,hp,rfl⟩⟩

/-- An actual projective rich line containing two distinct points of one
matching contains no point of either other matching: no type (2,1) occurs. -/
theorem actualRichLine_repeated_matching (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (Q : Finset Point) (hQ : ActualRichLine K hdet Q) (p q : MatchingIndex ι)
    (hp : configurationPoint K hdet p∈Q) (hq : configurationPoint K hdet q∈Q)
    (hpq : p≠q) (hlabel : p.1=q.1) : ActualOneMatching K hdet Q := by
  obtain ⟨S,hS,_,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp hQ
  have hp' := (mem_configurationPoints K hdet hfaith S p).mp hp
  have hq' := (mem_configurationPoints K hdet hfaith S q).mp hq
  refine ⟨p.1,?_⟩
  intro x hx
  exact matchingSecant_repeated_label K hdet hfaith S hS p q hp' hq' hpq hlabel x
    ((mem_configurationPoints K hdet hfaith S x).mp hx)

/-- Every actual rich projective line with at least four deck points is
monochromatic. In particular, there is no mixed four- or five-line. -/
theorem actualRichLine_large_oneMatching (K : ι → BinaryMatrix)
    (hdet : ∀i,(K i).det≠0) (hfaith : ∀ i j,Proportional (K i) (K j)→i=j)
    (Q : Finset Point) (hQ : ActualRichLine K hdet Q) (hlarge : 4≤Q.card) :
    ActualOneMatching K hdet Q := by
  obtain ⟨S,hS,_,rfl⟩ := (actualRichLine_iff K hdet hfaith Q).mp hQ
  have hc : 4≤S.card := by simpa only [configurationPoints_card K hdet hfaith] using hlarge
  obtain ⟨r,hr⟩ := matchingSecant_large_monochromatic K hdet hfaith S hS hc
  exact ⟨r,fun x hx => hr x ((mem_configurationPoints K hdet hfaith S x).mp hx)⟩

end
end Holant.Certificates.PlatonicIncidence
