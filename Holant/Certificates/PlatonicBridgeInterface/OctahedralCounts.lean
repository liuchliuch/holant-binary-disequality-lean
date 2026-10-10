import Holant.Certificates.PlatonicBridgeInterface.OctahedralRanks

/-! Cardinalities and disjoint rank classes of the actual normalized maps. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
open scoped Classical

def mapRank (Φ : Binary →ₗ[ℂ] FourTensor) : ℕ :=
  Matrix.rank (show Matrix (Fin 16) (Fin 4) ℂ from fun row k => Φ (quaternionBasis k) (TetrahedralDeck.words row))

noncomputable def rankTwoMaps : Finset (Binary →ₗ[ℂ] FourTensor) := by
  classical
  exact Finset.univ.image (fun i : Fin 6 => sourceMap (i.castAdd 24))

noncomputable def rankFourMaps : Finset (Binary →ₗ[ℂ] FourTensor) := by
  classical
  exact Finset.univ.image (fun i : Fin 24 => sourceMap (i.natAdd 6))

theorem rankTwoMaps_card : rankTwoMaps.card = 6 := by
  classical
  have hi : Function.Injective (fun i : Fin 6 => sourceMap (i.castAdd 24)) := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 30 => k.val) (sourceMap_injective h))
  rw [rankTwoMaps,Finset.card_image_of_injective _ hi]
  simp

theorem rankFourMaps_card : rankFourMaps.card = 24 := by
  classical
  have hi : Function.Injective (fun i : Fin 24 => sourceMap (i.natAdd 6)) := by
    intro i j h
    apply Fin.ext
    have he := congrArg (fun k : Fin 30 => k.val) (sourceMap_injective h)
    change 6+i.val=6+j.val at he
    omega
  rw [rankFourMaps,Finset.card_image_of_injective _ hi]
  simp

theorem rankTwoMaps_rank {Φ : Binary →ₗ[ℂ] FourTensor} (h : Φ ∈ rankTwoMaps) : mapRank Φ = 2 := by
  classical
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
  exact low_rank_two i

theorem rankFourMaps_rank {Φ : Binary →ₗ[ℂ] FourTensor} (h : Φ ∈ rankFourMaps) : mapRank Φ = 4 := by
  classical
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
  exact high_rank_four i

theorem rank_classes_disjoint : Disjoint rankTwoMaps rankFourMaps := by
  classical
  apply Finset.disjoint_left.mpr
  intro Φ h2 h4
  have htwo := rankTwoMaps_rank h2
  have hfour := rankFourMaps_rank h4
  omega

theorem normalizedMaps_partition : normalizedMaps = rankTwoMaps ∪ rankFourMaps := by
  classical
  ext Φ
  constructor
  · intro h
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    refine Fin.addCases (m := 6) (n := 24) (fun j => ?_) (fun j => ?_) i
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨i.castAdd 24,Finset.mem_univ _,rfl⟩
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨i.natAdd 6,Finset.mem_univ _,rfl⟩

theorem low_images_perm (i : Fin 6) :
    List.Perm [sourceMap (i.castAdd 24) (quaternionBasis 1),sourceMap (i.castAdd 24) (quaternionBasis 2),
      sourceMap (i.castAdd 24) (quaternionBasis 3)] [0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] := by
  rw [low_map_eq]
  exact TetrahedralBridge.low_images_perm i

theorem high_images (i : Fin 24) (j : Fin 3) :
    sourceMap (i.natAdd 6) (quaternionBasis j.succ) = R (sliceVector (ordering i j)) := by
  rw [sourceMap_next,high_orderedTuple,regular_eq_R]

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
