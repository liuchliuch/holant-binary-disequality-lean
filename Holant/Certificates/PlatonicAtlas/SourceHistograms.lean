import Holant.Certificates.PlatonicAtlas.ExternalTransitivity
import Holant.Certificates.PlatonicAtlas.Histograms
import Holant.Certificates.PlatonicAtlas.QuotientSpectrum

namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance sourceHistogramsPointDecidable : DecidableEq Point := Classical.decEq _
local instance sourceHistogramsSubmoduleDecidable : DecidableEq (Submodule ℂ FourTensor) := Classical.decEq _

 theorem standard_configuration_deck (g : PlatonicModel) :
    configurationPoints (representative g) (representative_det_ne_zero g) Finset.univ=deck g := by
  rw [deck,Finset.map_eq_image]
  rfl

 theorem external_configuration_deck :
    configurationPoints External.representative External.representative_det_ne_zero Finset.univ=External.deck := by
  rw [External.deck,Finset.map_eq_image]
  rfl

 theorem standard_quotientMultiplicity (g : PlatonicModel) (n : ℕ) :
    quotientMultiplicity (deck g) (basePoint 0) n=
      indexMultiplicity (representative g) (standardBase g) n := by
  rw [←standard_configuration_deck,basePoint_zero_eq_deck]
  exact quotientMultiplicity_eq_secantFibers _ _ (representative_proportional_faithful g) (standardBase g) n

 theorem external_quotientMultiplicity (n : ℕ) :
    quotientMultiplicity External.deck (External.deckPoint (0,0,0)) n=
      indexMultiplicity External.representative (0,0,0) n := by
  rw [←external_configuration_deck]
  exact quotientMultiplicity_eq_secantFibers _ _ external_representative_faithful (0,0,0) n

/-- Exact actual external quotient-direction histogram, including all absent sizes. -/
 theorem external_quotient_histogram (n : ℕ) :
    quotientMultiplicity External.deck (External.deckPoint (0,0,0)) n=
      if n=1 then 415 else if n=2 then 8 else 0 := by
  rw [external_quotientMultiplicity]
  by_cases h1 : n=1
  · subst n; exact external_index_histogram.1
  by_cases h2 : n=2
  · subst n; exact external_index_histogram.2.1
  simp only [if_neg h1,if_neg h2]
  exact external_index_histogram.2.2 n h1 h2

/-- Exact normalized octahedral quotient-direction histogram. -/
 theorem octahedral_quotient_histogram (n : ℕ) :
    quotientMultiplicity (deck .octahedral) (basePoint 0) n=
      if n=1 then 1645 else if n=2 then 32 else if n=3 then 6 else 0 := by
  rw [standard_quotientMultiplicity]
  by_cases h1 : n=1
  · subst n; exact octahedral_index_histogram.1
  by_cases h2 : n=2
  · subst n; exact octahedral_index_histogram.2.1
  by_cases h3 : n=3
  · subst n; exact octahedral_index_histogram.2.2.1
  simp only [if_neg h1,if_neg h2,if_neg h3]
  exact octahedral_index_histogram.2.2.2 n h1 h2 h3

/-- Exact normalized icosahedral quotient-direction histogram. -/
 theorem icosahedral_quotient_histogram (n : ℕ) :
    quotientMultiplicity (deck .icosahedral) (basePoint 0) n=
      if n=1 then 10591 else if n=2 then 80 else if n=4 then 12 else 0 := by
  rw [standard_quotientMultiplicity]
  by_cases h1 : n=1
  · subst n; exact icosahedral_index_histogram.1
  by_cases h2 : n=2
  · subst n; exact icosahedral_index_histogram.2.1
  by_cases h4 : n=4
  · subst n; exact icosahedral_index_histogram.2.2.1
  simp only [if_neg h1,if_neg h2,if_neg h4]
  exact icosahedral_index_histogram.2.2.2 n h1 h2 h4

 theorem external_base_literal : External.deckPoint (0,0,0)=normalMatchingPoint 0 := by
  change Projectivization.mk ℂ (matchingTensor 0 (External.representative 0) (External.representative 0)) _=_
  simp only [External.representative_identity]
  rfl

end
end Holant.Certificates.PlatonicAtlas
