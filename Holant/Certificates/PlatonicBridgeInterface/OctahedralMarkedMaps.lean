import Holant.Certificates.PlatonicBridgeInterface.OctahedralTransport
import Holant.Certificates.PlatonicBridgeInterface.OctahedralActualMap

/-! Exhaustive physical normalized maps in every source marked coordinate form. -/
namespace Holant.Certificates.PlatonicBridgeInterface.Octahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def physicalMap (f : Form) (i : Fin 30) : Binary →ₗ[ℂ] FourTensor := markMap f (sourceMap i)
def MarkedNormalized (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) : Prop := Normalized (unmarkMap f Φ)

def SourceHypotheses (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) : Prop :=
  (Φ (thetaEquiv f TetrahedralBridge.normalPlus) = coefficientEquiv f A ∧
    Φ (thetaEquiv f TetrahedralBridge.normalMinus) = coefficientEquiv f (-B)) ∧
  ∀ j : Fin 3, bridgeConditions .octahedral
    ((coefficientEquiv f).symm (Φ (thetaEquiv f (quaternionBasis j.succ))))

theorem marked_normalized_iff_source (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) :
    MarkedNormalized f Φ ↔ SourceHypotheses f Φ := by
  rw [MarkedNormalized,normalized_iff_source]
  have ha : unmarkMap f Φ TetrahedralBridge.normalPlus = A ↔
      Φ (thetaEquiv f TetrahedralBridge.normalPlus) = coefficientEquiv f A := by
    change (coefficientEquiv f).symm _ = A ↔ _
    exact (coefficientEquiv f).symm_apply_eq
  have hb : unmarkMap f Φ TetrahedralBridge.normalMinus = -B ↔
      Φ (thetaEquiv f TetrahedralBridge.normalMinus) = coefficientEquiv f (-B) := by
    change (coefficientEquiv f).symm _ = -B ↔ _
    exact (coefficientEquiv f).symm_apply_eq
  change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
  rw [ha,hb]
  rfl

theorem marked_normalized_iff (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) :
    MarkedNormalized f Φ ↔ ∃ i : Fin 30, Φ = physicalMap f i := by
  rw [MarkedNormalized,normalized_iff]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨i,by rw [←mark_unmark f Φ,hi]; rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨i,unmark_mark f _⟩

theorem physicalMap_injective (f : Form) : Function.Injective (physicalMap f) :=
  (markMap_injective f).comp sourceMap_injective

theorem physicalMap_rank (f : Form) (i : Fin 30) : mapRank (physicalMap f i) = mapRank (sourceMap i) :=
  markMap_rank f _

def markedNormalizedMaps (f : Form) : Finset (Binary →ₗ[ℂ] FourTensor) := Finset.univ.image (physicalMap f)
def markedRankTwoMaps (f : Form) : Finset (Binary →ₗ[ℂ] FourTensor) :=
  Finset.univ.image (fun i : Fin 6 => physicalMap f (i.castAdd 24))
def markedRankFourMaps (f : Form) : Finset (Binary →ₗ[ℂ] FourTensor) :=
  Finset.univ.image (fun i : Fin 24 => physicalMap f (i.natAdd 6))

theorem mem_markedNormalizedMaps (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor) :
    Φ ∈ markedNormalizedMaps f ↔ SourceHypotheses f Φ := by
  rw [←marked_normalized_iff_source,marked_normalized_iff]
  simp [markedNormalizedMaps,eq_comm]

theorem markedNormalizedMaps_card (f : Form) : (markedNormalizedMaps f).card = 30 := by
  rw [markedNormalizedMaps,Finset.card_image_of_injective _ (physicalMap_injective f)]
  simp

theorem markedRankTwoMaps_card (f : Form) : (markedRankTwoMaps f).card = 6 := by
  have hi : Function.Injective (fun i : Fin 6 => physicalMap f (i.castAdd 24)) := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 30 => k.val) (physicalMap_injective f h))
  rw [markedRankTwoMaps,Finset.card_image_of_injective _ hi]
  simp

theorem markedRankFourMaps_card (f : Form) : (markedRankFourMaps f).card = 24 := by
  have hi : Function.Injective (fun i : Fin 24 => physicalMap f (i.natAdd 6)) := by
    intro i j h
    apply Fin.ext
    have he := congrArg (fun k : Fin 30 => k.val) (physicalMap_injective f h)
    change 6+i.val=6+j.val at he
    omega
  rw [markedRankFourMaps,Finset.card_image_of_injective _ hi]
  simp

theorem markedRankTwoMaps_rank (f : Form) {Φ : Binary →ₗ[ℂ] FourTensor}
    (h : Φ ∈ markedRankTwoMaps f) : mapRank Φ = 2 := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
  rw [physicalMap_rank]
  exact low_rank_two i

theorem markedRankFourMaps_rank (f : Form) {Φ : Binary →ₗ[ℂ] FourTensor}
    (h : Φ ∈ markedRankFourMaps f) : mapRank Φ = 4 := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
  rw [physicalMap_rank]
  exact high_rank_four i

theorem marked_rank_classes_disjoint (f : Form) : Disjoint (markedRankTwoMaps f) (markedRankFourMaps f) := by
  apply Finset.disjoint_left.mpr
  intro Φ h2 h4
  have htwo := markedRankTwoMaps_rank f h2
  have hfour := markedRankFourMaps_rank f h4
  omega

theorem markedNormalizedMaps_partition (f : Form) :
    markedNormalizedMaps f = markedRankTwoMaps f ∪ markedRankFourMaps f := by
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

theorem marked_full_rank_iff (f : Form) (Φ : Binary →ₗ[ℂ] FourTensor)
    (hn : SourceHypotheses f Φ) :
    mapRank Φ = 4 ↔ ∃ i : Fin 24, Φ = physicalMap f (i.natAdd 6) := by
  constructor
  · intro hr
    have hm := (mem_markedNormalizedMaps f Φ).mpr hn
    rw [markedNormalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2 | h4
    · have htwo := markedRankTwoMaps_rank f h2
      omega
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h4
      exact ⟨i,hi.symm⟩
  · rintro ⟨i,rfl⟩
    rw [physicalMap_rank]
    exact high_rank_four i

theorem markedRankTwoMaps_eq_filter (f : Form) :
    markedRankTwoMaps f = (markedNormalizedMaps f).filter (fun Φ => mapRank Φ < 4) := by
  ext Φ
  constructor
  · intro h2
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · rw [markedNormalizedMaps_partition]
      exact Finset.mem_union_left _ h2
    · rw [markedRankTwoMaps_rank f h2]
      norm_num
  · intro h
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp h
    rw [markedNormalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2 | h4
    · exact h2
    · rw [markedRankFourMaps_rank f h4] at hr
      omega

theorem marked_six_rank_deficient (f : Form) :
    ((markedNormalizedMaps f).filter (fun Φ => mapRank Φ < 4)).card = 6 := by
  rw [←markedRankTwoMaps_eq_filter,markedRankTwoMaps_card]

theorem markedRankFourMaps_eq_filter (f : Form) :
    markedRankFourMaps f = (markedNormalizedMaps f).filter (fun Φ => mapRank Φ = 4) := by
  ext Φ
  constructor
  · intro h4
    apply Finset.mem_filter.mpr
    refine ⟨?_,markedRankFourMaps_rank f h4⟩
    rw [markedNormalizedMaps_partition]
    exact Finset.mem_union_right _ h4
  · intro h
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp h
    rw [markedNormalizedMaps_partition] at hm
    rcases Finset.mem_union.mp hm with h2 | h4
    · rw [markedRankTwoMaps_rank f h2] at hr
      norm_num at hr
    · exact h4

theorem marked_twenty_four_full_rank (f : Form) :
    ((markedNormalizedMaps f).filter (fun Φ => mapRank Φ = 4)).card = 24 := by
  rw [←markedRankFourMaps_eq_filter,markedRankFourMaps_card]

end
end Holant.Certificates.PlatonicBridgeInterface.Octahedral
