import Holant.Certificates.PlatonicIncidence.MonochromaticMarked
import Holant.Certificates.PlatonicIncidence.MonochromaticOpposite
import Holant.Certificates.PlatonicIncidence.MonochromaticExclusions

/-! Complete source deck-line rows: semantic rainbow counts from A.18 together
with the exhaustive actual-projective monochromatic classification and counts. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
noncomputable section

theorem tetrahedral_complete_deck_counts :
    {Q : Finset Point | RainbowLine .tetrahedral Q}.ncard=1728 ∧
    standardMonochromaticCount .tetrahedral 3=1152 ∧
    standardMonochromaticCount .tetrahedral 4=0 ∧ standardMonochromaticCount .tetrahedral 5=0 :=
  ⟨by simpa [size] using all_rainbow_lines_card .tetrahedral,standard_semantic_monochromatic_counts.1⟩

theorem octahedral_complete_deck_counts :
    {Q : Finset Point | RainbowLine .octahedral Q}.ncard=13824 ∧
    standardMonochromaticCount .octahedral 3=4608 ∧
    standardMonochromaticCount .octahedral 4=2592 ∧ standardMonochromaticCount .octahedral 5=0 :=
  ⟨by simpa [size] using all_rainbow_lines_card .octahedral,standard_semantic_monochromatic_counts.2.1⟩

theorem icosahedral_complete_deck_counts :
    {Q : Finset Point | RainbowLine .icosahedral Q}.ncard=216000 ∧
    standardMonochromaticCount .icosahedral 3=72000 ∧
    standardMonochromaticCount .icosahedral 4=0 ∧ standardMonochromaticCount .icosahedral 5=25920 :=
  ⟨by simpa [size] using all_rainbow_lines_card .icosahedral,standard_semantic_monochromatic_counts.2.2⟩

/-- Includes O', O_dt and O_td using their literal current representatives. -/
theorem marked_complete_deck_counts (f : Form) :
    {Q : Finset Point | MarkedRainbowLine f Q}.ncard=13824 ∧
    markedMonochromaticCount f 3=4608 ∧
    markedMonochromaticCount f 4=2592 ∧ markedMonochromaticCount f 5=0 :=
  ⟨marked_all_lines_card f,marked_semantic_monochromatic_counts f⟩

theorem external_complete_deck_counts :
    {Q : Finset Point | ExternalRainbowLine Q}.ncard=0 ∧
    externalMonochromaticCount 3=1152 ∧ externalMonochromaticCount 4=0 ∧ externalMonochromaticCount 5=0 :=
  ⟨external_table.2.1,external_semantic_monochromatic_counts⟩

/-- The source's four columns: rainbow three-lines, then monochromatic
three-, four-, and five-lines, all counted as actual projective point sets. -/
def DeckLineCounts (R : Finset Point→Prop) (M : ℕ→ℕ) (a b c d : ℕ) : Prop :=
  {Q : Finset Point | R Q}.ncard=a ∧ M 3=b ∧ M 4=c ∧ M 5=d

/-- All source rows in one semantic count table. Completeness, disjointness,
maximality and excluded types are established by the accompanying APIs. -/
theorem complete_deck_count_table :
    DeckLineCounts (RainbowLine .tetrahedral) (standardMonochromaticCount .tetrahedral) 1728 1152 0 0 ∧
    DeckLineCounts (RainbowLine .octahedral) (standardMonochromaticCount .octahedral) 13824 4608 2592 0 ∧
    (∀f : Form,DeckLineCounts (MarkedRainbowLine f) (markedMonochromaticCount f) 13824 4608 2592 0) ∧
    DeckLineCounts ExternalRainbowLine externalMonochromaticCount 0 1152 0 0 ∧
    DeckLineCounts (RainbowLine .icosahedral) (standardMonochromaticCount .icosahedral) 216000 72000 0 25920 ∧
    DeckLineCounts Opposite.RainbowLine oppositeMonochromaticCount 216000 72000 0 25920 :=
  ⟨tetrahedral_complete_deck_counts,octahedral_complete_deck_counts,marked_complete_deck_counts,
    external_complete_deck_counts,icosahedral_complete_deck_counts,opposite_complete_deck_counts⟩

end
end Holant.Certificates.PlatonicIncidence
