import Holant.Certificates.TetrahedralBridge.Counts
import Holant.Certificates.TetrahedralBridge.Normalization

/-! Full Lemma9.14, including unrestricted six-point completeness, exhaustive
actual-map count12, no duplicates, and the true rank2/rank4 split. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
open scoped Classical

structure TetrahedralBridgeCertificate : Prop where
  exact_bridge : ∀ W : FourTensor, bridgeConditions .tetrahedral W ↔ ∃ i : Fin 6, W = candidate i
  six_bridge_points : bridgePoints.card = 6
  source_normalization : ∀ Φ : Binary →ₗ[ℂ] FourTensor,
    ((Φ normalPlus = A ∧ Φ normalMinus = -B) ∧
      ∀ j : Fin 3, bridgeConditions .tetrahedral (Φ (quaternionBasis j.succ))) ↔ Φ ∈ normalizedMaps
  twelve_actual_maps : normalizedMaps.card = 12
  complete_rank_partition : normalizedMaps = rankTwoMaps ∪ rankFourMaps
  no_overlap : Disjoint rankTwoMaps rankFourMaps
  six_rank_two : rankTwoMaps.card = 6
  six_rank_four : rankFourMaps.card = 6
  actual_rank_two : ∀ Φ ∈ rankTwoMaps, mapRank Φ = 2
  actual_rank_four : ∀ Φ ∈ rankFourMaps, mapRank Φ = 4
  exact_exceptionals : ∀ i : Fin 6,
    List.Perm [sourceMap (i.castAdd 6) (quaternionBasis 1),sourceMap (i.castAdd 6) (quaternionBasis 2),
      sourceMap (i.castAdd 6) (quaternionBasis 3)] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B]
  exact_regulars : ∀ i : Fin 6,
    List.Perm [sourceMap (i.natAdd 6) (quaternionBasis 1),sourceMap (i.natAdd 6) (quaternionBasis 2),
      sourceMap (i.natAdd 6) (quaternionBasis 3)] [regular 0,regular 1,regular 2]
  actual_contractions : ∀ i : Fin 12, ∀ U : Binary,
    sourceMap i U = Signature.contract U (reconstruct (sourceImages i))

/-- Full current tetrahedral bridge lemma. Every cardinality counts actual
complex coefficient maps, and every such map is identified with actual cards. -/
theorem tetrahedral_bridge : TetrahedralBridgeCertificate where
  exact_bridge := bridge_iff
  six_bridge_points := bridgePoints_card
  source_normalization Φ := (normalized_iff_source Φ).symm.trans (mem_normalizedMaps Φ).symm
  twelve_actual_maps := normalizedMaps_card
  complete_rank_partition := normalizedMaps_partition
  no_overlap := rank_classes_disjoint
  six_rank_two := rankTwoMaps_card
  six_rank_four := rankFourMaps_card
  actual_rank_two := fun _ h => rankTwoMaps_rank h
  actual_rank_four := fun _ h => rankFourMaps_rank h
  exact_exceptionals := low_images_perm
  exact_regulars := high_images_perm
  actual_contractions := sourceMap_contract

end
end Holant.Certificates.TetrahedralBridge
