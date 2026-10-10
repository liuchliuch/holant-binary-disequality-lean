import Holant.Certificates.TetrahedralPreservers.RankOne
import Mathlib.LinearAlgebra.Projectivization.Basic

/-! Complete rank-one classification for the actual standard and external
tetrahedral sets. The final cardinality is a count of projective complex maps. -/
noncomputable section
namespace Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

theorem coordinates_basis (i : Fin 4) : coordinates (Matrix.of (quaternionBasis i)) = Pi.single i 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinates_apply,quaternionCoefficient,quaternionBasis,Q0,Q1,Q2,Q3,
      Holant.Signature.equality,Pi.single_apply] <;> ring_nf <;> simp [Complex.I_sq]

theorem standard_axis (i : Fin 4) : Pi.single i 1 ∈ Standard := by
  rw [← coordinates_basis]
  exact ⟨_,quaternion_axis_direction .tetrahedral i,rfl⟩

theorem standard_detects : Detects Standard := by
  intro v hv
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  refine ⟨Pi.single i 1,standard_axis i,?_⟩
  rw [pairing_axis]
  apply mul_ne_zero _ hi
  intro h
  have := signs_square i
  simp [h] at this

theorem external_printed_mem (K : BinaryMatrix) (h : RainbowOrbit.External.PrintedBase K) :
    coordinates K ∈ External := by
  refine ⟨K,?_,rfl⟩
  exact (RainbowOrbit.External.direction_iff_printed K).mpr ⟨1,one_ne_zero,K,h,by simp⟩

theorem external_detects : Detects External := by
  intro v hv
  by_contra! h
  have h0 := h (coordinates (Matrix.of Q0)) (external_printed_mem _ (by
    rw [RainbowOrbit.External.printedBase_literal]; exact Or.inl rfl))
  have h1 := h (coordinates (Matrix.of Q1)) (external_printed_mem _ (by
    rw [RainbowOrbit.External.printedBase_literal]; exact Or.inr (Or.inl rfl)))
  have h2 := h (coordinates (Matrix.of Q2 + Matrix.of Q3)) (external_printed_mem _ (by
    rw [RainbowOrbit.External.printedBase_literal]
    exact Or.inr (Or.inr (Or.inl ⟨false,by simp [signBit]⟩))))
  have h3 := h (coordinates (Matrix.of Q2 - Matrix.of Q3)) (external_printed_mem _ (by
    rw [RainbowOrbit.External.printedBase_literal]
    exact Or.inr (Or.inr (Or.inl ⟨true,by simp [signBit,sub_eq_add_neg]⟩))))
  norm_num [pairing,frobeniusSigns,coordinates_apply,quaternionCoefficient,
    Q0,Q1,Q2,Q3,Holant.Signature.equality,Fin.sum_univ_succ] at h0 h1 h2 h3
  ring_nf at h2 h3
  simp [Complex.I_sq] at h2 h3
  apply hv
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · change v 2 = 0
    linear_combination (h2+h3)/2
  · change v 3 = 0
    linear_combination (h3-h2)/2

theorem standardPoint_ne_zero (k : Fin 12) : standardPoint k ≠ 0 := by
  intro h
  apply RainbowOrbit.representative_ne_zero .tetrahedral k
  exact coordinates.injective (by simpa [standardPoint] using h)

theorem externalPoint_ne_zero (k : Fin 12) : externalPoint k ≠ 0 := by
  intro h
  apply RainbowOrbit.External.representative_ne_zero k
  exact coordinates.injective (by simpa [externalPoint] using h)

theorem standardPoint_mem (k : Fin 12) : standardPoint k ∈ Standard :=
  (standard_iff _).mpr ⟨k,1,one_ne_zero,by simp⟩

theorem externalPoint_mem (k : Fin 12) : externalPoint k ∈ External :=
  (external_iff _).mpr ⟨k,1,one_ne_zero,by simp⟩

theorem standardPoint_projectively_injective (i j : Fin 12) (c : ℂ)
    (h : standardPoint i = c • standardPoint j) : i=j := by
  apply RainbowOrbit.projectively_injective .tetrahedral i j c
  apply coordinates.injective
  simpa [standardPoint] using h

theorem externalPoint_projectively_injective (i j : Fin 12) (c : ℂ)
    (h : externalPoint i = c • externalPoint j) : i=j := by
  apply RainbowOrbit.External.projectively_injective i j c
  apply coordinates.injective
  simpa [externalPoint] using h

theorem outer_smul (u v : V) (c d : ℂ) : outer (c • u) (d • v) = (c*d) • outer u v := by
  ext i j
  simp [outer]
  ring

/-- Every rank-one external preserver is a nonzero scalar multiple of precisely
one of the 12 by 12 Frobenius outer-product representatives. -/
theorem external_rank_one_complete (A : End) (hA : A.rank = 1) :
    TwoSided External A ↔ ∃ i j : Fin 12, ∃ c : ℂ, c ≠ 0 ∧
      A = c • outer (externalPoint i) (externalPoint j) := by
  rw [rank_one_twoSided_iff external_saturated external_detects A hA]
  constructor
  · rintro ⟨u,v,hu,hv,rfl⟩
    obtain ⟨i,c,hc,rfl⟩ := (external_iff u).mp hu
    obtain ⟨j,d,hd,rfl⟩ := (external_iff v).mp hv
    exact ⟨i,j,c*d,mul_ne_zero hc hd,outer_smul _ _ c d⟩
  · rintro ⟨i,j,c,hc,rfl⟩
    refine ⟨c • externalPoint i,externalPoint j,
      external_saturated (externalPoint_mem i) hc,externalPoint_mem j,?_⟩
    simpa using (outer_smul (externalPoint i) (externalPoint j) c 1).symm

theorem standard_rank_one_complete (A : End) (hA : A.rank = 1) :
    TwoSided Standard A ↔ ∃ i j : Fin 12, ∃ c : ℂ, c ≠ 0 ∧
      A = c • outer (standardPoint i) (standardPoint j) := by
  rw [rank_one_twoSided_iff standard_saturated standard_detects A hA]
  constructor
  · rintro ⟨u,v,hu,hv,rfl⟩
    obtain ⟨i,c,hc,rfl⟩ := (standard_iff u).mp hu
    obtain ⟨j,d,hd,rfl⟩ := (standard_iff v).mp hv
    exact ⟨i,j,c*d,mul_ne_zero hc hd,outer_smul _ _ c d⟩
  · rintro ⟨i,j,c,hc,rfl⟩
    refine ⟨c • standardPoint i,standardPoint j,
      standard_saturated (standardPoint_mem i) hc,standardPoint_mem j,?_⟩
    simpa using (outer_smul (standardPoint i) (standardPoint j) c 1).symm

end Holant.Certificates.TetrahedralPreservers
