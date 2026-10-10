import Holant.Certificates.PlatonicBridgeInterface.OctahedralExits

/-! A.27(i): unrestricted twelve-point bridge, exact physical normalized-map
partition in every marked form, and the fixed actual current-form exits. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

 theorem ordering_exhaustive : ∀ frame : Fin 4, ∀ order : Fin 6,
    ∃ i : Fin 24, ∀ j : Fin 3, ordering i j = frames frame (permutation order j) := by decide +kernel

 theorem frames_injective : Function.Injective frames := by decide +kernel

 theorem four_frames : (Finset.univ.image frames).card = 4 := by
  rw [Finset.card_image_of_injective _ frames_injective]
  simp

structure Clause : Prop where
  unrestricted_bridge : ∀ W : FourTensor,
    bridgeConditions .octahedral W ↔ ∃ i : Fin 12, W = candidate i
  twelve_distinct_points : bridgePoints.card = 12
  actual_map_rank : ∀ Φ : Binary →ₗ[ℂ] FourTensor,
    mapRank Φ = Module.finrank ℂ (LinearMap.range Φ)
  source_normalization : ∀ f : Form, ∀ Φ : Binary →ₗ[ℂ] FourTensor,
    MarkedNormalized f Φ ↔ SourceHypotheses f Φ
  exhaustive_physical_maps : ∀ f : Form, ∀ Φ : Binary →ₗ[ℂ] FourTensor,
    SourceHypotheses f Φ ↔ ∃ i : Fin 30, Φ = physicalMap f i
  thirty_distinct_maps : ∀ f : Form, (markedNormalizedMaps f).card = 30
  six_deficient : ∀ f : Form,
    ((markedNormalizedMaps f).filter (fun Φ => mapRank Φ < 4)).card = 6
  deficient_rank_two : ∀ f : Form, ∀ Φ ∈ markedRankTwoMaps f, mapRank Φ = 2
  twenty_four_full : ∀ f : Form,
    ((markedNormalizedMaps f).filter (fun Φ => mapRank Φ = 4)).card = 24
  full_rank_four : ∀ f : Form, ∀ Φ ∈ markedRankFourMaps f, mapRank Φ = 4
  full_rank_exhaustive : ∀ f : Form, ∀ Φ : Binary →ₗ[ℂ] FourTensor,
    SourceHypotheses f Φ → (mapRank Φ = 4 ↔ ∃ i : Fin 24, Φ = physicalMap f (i.natAdd 6))
  displayed_frames : frames = ![![0,1,2],![0,7,8],![1,5,6],![2,3,4]]
  four_distinct_frames : (Finset.univ.image frames).card = 4
  six_orders_each_frame : ∀ frame : Fin 4, ∀ order : Fin 6,
    ∃ i : Fin 24, ∀ j : Fin 3, ordering i j = frames frame (permutation order j)
  original_frame_tensors : ∀ j : Fin 9,
    regular j = OctahedralSeparator.complexTensor (OctahedralSeparator.regular j)
  original_six_port_maps : ∀ f : Form, ∀ i : Fin 24,
    physicalMap f (i.natAdd 6) = actualMap (OctahedralSeparator.complexTensor
      (OctahedralSeparator.fullAncestor f ⟨i.val/6,by omega⟩ ⟨i.val%6,by omega⟩))
  fixed_standard_kernel : fixedKernel 0 = Q0+Q1
  fixed_actual_kernel : ∀ f : Form, fixedKernel f = thetaEquiv f (Q0+Q1)
  fixed_kernel_available : ∀ f : Form, OctahedralSeparator.Direction f (Matrix.of (fixedKernel f))
  fixed_first_card : ∀ f : Form, ∀ h : Signature ℂ 6,
    SourceHypotheses f (actualMap h) → mapRank (actualMap h) = 4 →
    ∃ i : Fin 24, Signature.contract (fixedKernel f) h =
      OctahedralSeparator.complexTensor
        (OctahedralSeparator.coefficientCard f ((ordering i 0).castAdd 6))
  unmixed_eight_vertex : ∀ f : Fin 2, ∀ h : Signature ℂ 6,
    SourceHypotheses (f.castAdd 2) (actualMap h) → mapRank (actualMap h) = 4 →
    OctahedralSeparator.EndpointExit (f.castAdd 2) h
  unmixed_fixed_network : ∀ f : Fin 2, ∀ h : Signature ℂ 6,
    SourceHypotheses (f.castAdd 2) (actualMap h) → mapRank (actualMap h) = 4 →
    ∃ t : Signature ℂ 4,
      OctahedralSeparator.BoundedNativeRealization (f.castAdd 2) h (fixedKernel (f.castAdd 2)) t ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
      ∀ r : Fin 3, (flatten r t).rank = 2
  all_form_exits : ∀ f : Form, ∀ h : Signature ℂ 6,
    SourceHypotheses f (actualMap h) → mapRank (actualMap h) = 4 → OctahedralSeparator.Resolved f h
  all_form_fixed_networks : ∀ f : Form, ∀ h : Signature ℂ 6,
    SourceHypotheses f (actualMap h) → mapRank (actualMap h) = 4 → FixedKernelExit f h

theorem complete_clause : Clause where
  unrestricted_bridge := bridge_iff
  twelve_distinct_points := bridgePoints_card
  actual_map_rank := mapRank_eq_finrank
  source_normalization := marked_normalized_iff_source
  exhaustive_physical_maps := fun f Φ => (marked_normalized_iff_source f Φ).symm.trans (marked_normalized_iff f Φ)
  thirty_distinct_maps := markedNormalizedMaps_card
  six_deficient := marked_six_rank_deficient
  deficient_rank_two := fun f _ h => markedRankTwoMaps_rank f h
  twenty_four_full := marked_twenty_four_full_rank
  full_rank_four := fun f _ h => markedRankFourMaps_rank f h
  full_rank_exhaustive := marked_full_rank_iff
  displayed_frames := rfl
  four_distinct_frames := four_frames
  six_orders_each_frame := ordering_exhaustive
  original_frame_tensors := regular_eq_source
  original_six_port_maps := physicalMap_full_ancestor
  fixed_standard_kernel := fixedKernel_standard
  fixed_actual_kernel := fixedKernel_theta
  fixed_kernel_available := fixedKernel_available
  fixed_first_card := actual_fixed_first_card
  unmixed_eight_vertex := actual_unmixed_eight_vertex
  unmixed_fixed_network := actual_unmixed_fixed_endpoint
  all_form_exits := actual_full_rank_exits
  all_form_fixed_networks := actual_fixed_kernel_exit

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
