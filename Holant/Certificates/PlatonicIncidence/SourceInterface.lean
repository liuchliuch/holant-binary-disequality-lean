import Holant.Certificates.PlatonicIncidence.MonochromaticInterface
import Holant.Certificates.PlatonicIncidence.ProjectiveDomainGraph
import Holant.Certificates.PlatonicIncidence.OrderedWitnesses

/-! Full source Theorem A.20 (paper1.tex 17845–17891).

(i) Complete semantic counts of ordinary maximal rich actual projective deck
lines, all matching-label exclusions, and every unlisted-size exclusion.
(ii) Actual current-group port witnesses from A.18 in all standard/marked
forms, and the literal opposite-I transitivity with exact native-X networks.
(iii) Nonempty connected kernel-deleted graphs on actual projective domain
points for every complex subspace of dimension at most two. Coefficient
similarities in the dictionary are analytic and are never physical resources.

This module does not claim the additional A.19 rich-line intersection-graph
edge counts, quotient-direction histograms or left/right domain-line orbits. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- The exact six source rows, with the marked quantifier covering O', dt and td. -/
def SourceCountTable : Prop :=
  DeckLineCounts (RainbowLine .tetrahedral) (standardMonochromaticCount .tetrahedral) 1728 1152 0 0 ∧
  DeckLineCounts (RainbowLine .octahedral) (standardMonochromaticCount .octahedral) 13824 4608 2592 0 ∧
  (∀f : Form,DeckLineCounts (MarkedRainbowLine f) (markedMonochromaticCount f) 13824 4608 2592 0) ∧
  DeckLineCounts ExternalRainbowLine externalMonochromaticCount 0 1152 0 0 ∧
  DeckLineCounts (RainbowLine .icosahedral) (standardMonochromaticCount .icosahedral) 216000 72000 0 25920 ∧
  DeckLineCounts Opposite.RainbowLine oppositeMonochromaticCount 216000 72000 0 25920

def SourceLineCompleteness : Prop :=
  (∀g Q,ActualRichLine (representative g) (representative_det_ne_zero g) Q ↔
    Q∈standardMonochromaticLines g ∨ RainbowLine g Q) ∧
  (∀f Q,ActualRichLine (markedRepresentative f) (markedRepresentative_det f) Q ↔
    Q∈markedMonochromaticLines f ∨ MarkedRainbowLine f Q) ∧
  (∀Q,ActualRichLine External.representative External.representative_det_ne_zero Q ↔
    Q∈externalMonochromaticLines) ∧
  (∀Q,ActualRichLine OppositeIcosahedral.oppositeRepresentative OppositeIcosahedral.oppositeRepresentative_det Q ↔
    Q∈oppositeMonochromaticLines ∨ Opposite.RainbowLine Q)

/-- Genuine native-X witnesses using only the original point and fixed actual
current-group binary resources. The four retained ports keep their order. -/
def SourcePhysicalWitnesses : Prop :=
  (∀g p,Rainbow g p → OrderedPhysicalWitness (representative g) (fun r => (p r).rep) base) ∧
  (∀f p,MarkedRainbow f p → OrderedPhysicalWitness (markedRepresentative f)
    (fun r => (p r).rep) (markedInitial f)) ∧
  (∀p q,Opposite.Rainbow p → Opposite.Rainbow q →
    OrderedPhysicalWitness OppositeIcosahedral.oppositeRepresentative
      (fun r => (p r).rep) (fun r => (q r).rep))

/-- This stronger analytic statement includes every source marked row via
identity, thetaEquiv, oppositeEquiv and the retained-I kappaEquiv. -/
def SourceKernelDeletion : Prop :=
  ∀g (e : Mat ≃ₗ[ℂ] Mat) (W : Submodule ℂ Mat),Module.finrank ℂ W≤2 →
    ((projectiveGraph (fun i => e (representative g i))).induce
      (projectiveDeleted (fun i => e (representative g i))
        (transformed_representative_nonzero g e) W)).Connected

theorem source_A20 : SourceCountTable ∧ SourceLineCompleteness ∧
    SourcePhysicalWitnesses ∧ SourceKernelDeletion :=
  ⟨complete_deck_count_table,
    ⟨standard_actual_rich_complete_iff,marked_actual_rich_complete_iff,
      external_actual_rich_complete_iff,opposite_actual_rich_complete_iff⟩,
    ⟨ordered_standard_normalization,ordered_marked_normalization,ordered_opposite_transitivity⟩,
    actual_kernel_deleted_connected⟩

end
end Holant.Certificates.PlatonicIncidence
