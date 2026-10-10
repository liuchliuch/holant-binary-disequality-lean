import Holant.Certificates.PlatonicAtlas.QuotientFibers
import Holant.Certificates.PlatonicAtlas.RichIncidenceCounts

/-! The three source quotient histograms, derived from the complete actual
secant partition and the established rich-line incidences. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable
local instance histogramShapesPointDecidable : DecidableEq Point := Classical.decEq _
local instance histogramShapesSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 abbrev indexMultiplicity (K : ι→BinaryMatrix) (p : MatchingIndex ι) (n : ℕ) : ℕ :=
  fiberMultiplicity (Finset.univ.erase p) (secantMap K p) n

 theorem indexMultiplicity_rich (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p : MatchingIndex ι) (n : ℕ) (hn : 2≤n) :
    indexMultiplicity K p n=
      {Q : Finset Point | ActualRichLine K hdet Q ∧ configurationPoint K hdet p∈Q ∧ Q.card=n+1}.ncard :=
  (actual_rich_fiber_count K hdet hfaith p n hn).symm

 theorem fiber_actual_line (K : ι→BinaryMatrix) (hdet : ∀i,(K i).det≠0)
    (hfaith : ∀i j,Proportional (K i) (K j)→i=j)
    (p : MatchingIndex ι) (B : Finset (MatchingIndex ι)) (hB : B∈secantFibers K p) (hc : 2≤B.card) :
    ActualRichLine K hdet (configurationPoints K hdet (insert p B)) ∧
      (configurationPoints K hdet (insert p B)).card=B.card+1 := by
  have hcard := (configurationPoints_card K hdet hfaith (insert p B)).trans (secantFiber_card_add_one K p B hB)
  exact ⟨(actualRichLine_iff K hdet hfaith _).mpr
    ⟨insert p B,insert_secantFiber K hdet hfaith p B hB,by rw [secantFiber_card_add_one K p B hB]; omega,rfl⟩,hcard⟩

 theorem standard_fiber_sizes (g : PlatonicModel) (p : MatchingIndex (Fin (size g)))
    (B : Finset (MatchingIndex (Fin (size g)))) (hB : B∈secantFibers (representative g) p) :
    match g with
      | .tetrahedral => B.card=1 ∨ B.card=2
      | .octahedral => B.card=1 ∨ B.card=2 ∨ B.card=3
      | .icosahedral => B.card=1 ∨ B.card=2 ∨ B.card=4 := by
  have hpos := (fiberFamily_nonempty (Finset.univ.erase p) (secantMap (representative g) p) B hB).card_pos
  by_cases hc : B.card≤1
  · have he : B.card=1 := by omega
    cases g <;> simp [he]
  obtain ⟨hQ,hcard⟩ := fiber_actual_line (representative g) (representative_det_ne_zero g)
    (representative_proportional_faithful g) p B hB (by omega)
  rcases standard_actual_rich_classification g _ hQ with hm|hr
  · have hs := standard_monochromatic_sizes g _ hm
    cases g <;> simp only at hs ⊢ <;> omega
  · have hs := rainbowLine_three hr
    have he : B.card=2 := by omega
    cases g <;> simp [he]

 theorem external_fiber_sizes (p : MatchingIndex (Fin 12)) (B : Finset (MatchingIndex (Fin 12)))
    (hB : B∈secantFibers External.representative p) : B.card=1 ∨ B.card=2 := by
  have hpos := (fiberFamily_nonempty (Finset.univ.erase p) (secantMap External.representative p) B hB).card_pos
  by_cases hc : B.card≤1
  · exact Or.inl (by omega)
  obtain ⟨hQ,hcard⟩ := fiber_actual_line External.representative External.representative_det_ne_zero
    external_representative_faithful p B hB (by omega)
  have hs := external_monochromatic_size _ (external_actual_rich_classification _ hQ)
  exact Or.inr (by omega)


end
end Holant.Certificates.PlatonicAtlas
