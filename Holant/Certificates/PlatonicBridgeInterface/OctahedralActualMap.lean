import Holant.Certificates.PlatonicBridgeInterface.OctahedralCounts

/-! Arbitrary original six-port tensors are mapped by their actual contraction
map. The finite exhaustivity theorem therefore applies directly to real gadgets. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical

def actualMap (h : Signature ℂ 6) : Binary →ₗ[ℂ] FourTensor where
  toFun K := Signature.contract K h
  map_add' K L := by
    funext x
    simp [Signature.contract,add_mul,Finset.sum_add_distrib]
  map_smul' c K := by
    funext x
    simp [Signature.contract,mul_assoc,Finset.mul_sum]
    ring

@[simp] theorem actualMap_apply (h : Signature ℂ 6) (K : Binary) :
    actualMap h K = Signature.contract K h := rfl

theorem full_rank_iff (Φ : Binary →ₗ[ℂ] FourTensor) (hΦ : Normalized Φ) :
    mapRank Φ = 4 ↔ ∃ i : Fin 24, Φ = sourceMap (i.natAdd 6) := by
  constructor
  · intro hr
    have hm := (mem_normalizedMaps Φ).mpr hΦ
    rw [normalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2 | h4
    · have htwo := rankTwoMaps_rank h2
      omega
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h4
      exact ⟨i,hi.symm⟩
  · rintro ⟨i,rfl⟩
    exact high_rank_four i

theorem rankTwoMaps_eq_filter : rankTwoMaps = normalizedMaps.filter (fun Φ => mapRank Φ < 4) := by
  ext Φ
  constructor
  · intro h2
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · rw [normalizedMaps_partition]
      exact Finset.mem_union_left _ h2
    · rw [rankTwoMaps_rank h2]
      norm_num
  · intro h
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp h
    rw [normalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2 | h4
    · exact h2
    · rw [rankFourMaps_rank h4] at hr
      omega

theorem six_rank_deficient : (normalizedMaps.filter (fun Φ => mapRank Φ < 4)).card = 6 := by
  rw [←rankTwoMaps_eq_filter,rankTwoMaps_card]

theorem rankFourMaps_eq_filter : rankFourMaps = normalizedMaps.filter (fun Φ => mapRank Φ = 4) := by
  ext Φ
  constructor
  · intro h4
    apply Finset.mem_filter.mpr
    refine ⟨?_,rankFourMaps_rank h4⟩
    rw [normalizedMaps_partition]
    exact Finset.mem_union_right _ h4
  · intro h
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp h
    rw [normalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2 | h4
    · rw [rankTwoMaps_rank h2] at hr
      norm_num at hr
    · exact h4

theorem twenty_four_full_rank : (normalizedMaps.filter (fun Φ => mapRank Φ = 4)).card = 24 := by
  rw [←rankFourMaps_eq_filter,rankFourMaps_card]

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
