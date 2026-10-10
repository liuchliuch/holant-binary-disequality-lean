import Holant.Certificates.IcosahedralSeparator.ActualMap

/-! Complete structural part of Lemma9.29: the literal bridge, five source
frames, all normalized maps, and their actual ranks. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
open scoped Classical

structure IcosahedralBridgeCertificate : Prop where
  exact_bridge : ∀ W : FourTensor, bridgeConditions .icosahedral W ↔ ∃ i : Fin 18, W = candidate i
  eighteen_bridge_points : bridgePoints.card = 18
  source_normalization : ∀ Φ : Binary →ₗ[ℂ] FourTensor,
    ((Φ TetrahedralBridge.normalPlus = A ∧ Φ TetrahedralBridge.normalMinus = -B) ∧
      ∀ j : Fin 3, bridgeConditions .icosahedral (Φ (quaternionBasis j.succ))) ↔ Φ ∈ normalizedMaps
  thirty_six_actual_maps : normalizedMaps.card = 36
  complete_rank_partition : normalizedMaps = rankTwoMaps ∪ rankFourMaps
  no_overlap : Disjoint rankTwoMaps rankFourMaps
  six_rank_two : rankTwoMaps.card = 6
  thirty_rank_four : rankFourMaps.card = 30
  actual_rank_two : ∀ Φ ∈ rankTwoMaps, mapRank Φ = 2
  actual_rank_four : ∀ Φ ∈ rankFourMaps, mapRank Φ = 4
  rank_deficient_filter : (normalizedMaps.filter (fun Φ => mapRank Φ < 4)).card = 6
  full_rank_filter : (normalizedMaps.filter (fun Φ => mapRank Φ = 4)).card = 30
  exact_exceptionals : ∀ i : Fin 6,
    List.Perm [sourceMap (i.castAdd 30) (quaternionBasis 1),sourceMap (i.castAdd 30) (quaternionBasis 2),
      sourceMap (i.castAdd 30) (quaternionBasis 3)] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B]
  exact_regulars : ∀ i : Fin 30, ∀ j : Fin 3,
    sourceMap (i.natAdd 6) (quaternionBasis j.succ) = R (sourceFrame (ordering i j))
  five_frames : ∀ j k : Fin 15,
    dot (sourceFrame j) (sourceFrame k) = 0 ↔ j.val/3 = k.val/3 ∧ j ≠ k
  actual_contractions : ∀ i : Fin 36, ∀ K : Binary,
    sourceMap i K = Signature.contract K (ancestor i)

theorem icosahedral_bridge : IcosahedralBridgeCertificate where
  exact_bridge := bridge_iff
  eighteen_bridge_points := bridgePoints_card
  source_normalization Φ := (normalized_iff_source Φ).symm.trans (mem_normalizedMaps Φ).symm
  thirty_six_actual_maps := normalizedMaps_card
  complete_rank_partition := normalizedMaps_partition
  no_overlap := rank_classes_disjoint
  six_rank_two := rankTwoMaps_card
  thirty_rank_four := rankFourMaps_card
  actual_rank_two := fun _ h => rankTwoMaps_rank h
  actual_rank_four := fun _ h => rankFourMaps_rank h
  rank_deficient_filter := six_rank_deficient
  full_rank_filter := thirty_full_rank
  exact_exceptionals := low_images_perm
  exact_regulars := high_images
  five_frames := sourceFrame_orthogonal_iff
  actual_contractions := sourceMap_contract

end
end Holant.Certificates.IcosahedralSeparator
