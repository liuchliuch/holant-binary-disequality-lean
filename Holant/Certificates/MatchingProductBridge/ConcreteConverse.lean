import Holant.Certificates.MatchingProductBridge.ConcreteNecessity
import Holant.Certificates.MatchingProductBridge.Exceptionals

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem multiply_binaryInverse (U : Binary) (hU : Matrix.det (Matrix.of U) ≠ 0) :
    multiply U (binaryInverse U) = Q0 := by
  have hh := Matrix.mul_nonsing_inv (Matrix.of U) (isUnit_iff_ne_zero.mpr hU)
  have ho : Matrix.of (binaryInverse U) = (Matrix.of U)⁻¹ := rfl
  rw [← ho,← multiply_eq_matrix_mul] at hh
  exact congrArg (fun M : Matrix Bool Bool ℂ => fun a b => M a b) hh

theorem inverseTranspose_symmetric (U : Binary) (hs : transpose U = U) :
    transpose (binaryInverseTranspose U) = binaryInverseTranspose U := by
  have hU : (Matrix.of U).transpose = Matrix.of U := hs
  have hh : (Matrix.of U)⁻¹.transpose = (Matrix.of U)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv,hU]
  exact (congrArg (fun M : Matrix Bool Bool ℂ => fun a b => M a b) hh).symm

theorem matrixR_double (U : Binary) : (2 : ℂ) • matrixR U = P2 U (binaryInverseTranspose U) := by
  rw [matrixR,smul_smul]
  norm_num

/-- Every symmetric direction in each concrete Platonic family really satisfies all3cone tests. -/
theorem symmetric_direction_bridge (g : PlatonicModel) (U : Binary)
    (hU : groupDirection g U) (hs : transpose U = U) : bridgeConditions g (matrixR U) := by
  have hV := groupDirection_inverseTranspose g hU
  have hUV : multiply U (transpose (binaryInverseTranspose U)) = Q0 :=
    multiply_binaryInverse U (groupDirection_det_ne_zero g hU)
  have hyU := groupDirection_right_Q2 g hU
  have hyV := groupDirection_right_Q2 g hV
  refine ⟨?_,?_,?_⟩
  · exact matchingCone_smul g (matchingProduct_mem_cone g 2 hU hV) (1/2)
  · rw [matrixR_double,bridge_first U _ hUV]
    exact matchingProduct_mem_cone g 1 hyU hyV
  · rw [matrixR_double,bridge_second U _ hUV (inverseTranspose_symmetric U hs)]
    simpa [matchingProduct] using matchingCone_smul g (matchingProduct_mem_cone g 0 hyU hyV) (-1)

/-- The exact set equality asserted in A.15, for the literal T/O/I families. -/
theorem concrete_bridge_iff (g : PlatonicModel) (W : FourTensor) :
    bridgeConditions g W ↔
      W = 0 ∨ W = (1/2 : ℂ) • A ∨ W = (1/2 : ℂ) • B ∨
        ∃ U : Binary, groupDirection g U ∧ transpose U = U ∧ W = matrixR U := by
  constructor
  · exact concrete_bridge_necessity g W
  · rintro (rfl | rfl | rfl | ⟨U,hU,hs,rfl⟩)
    · exact zero_bridge g
    · exact half_A_bridge g
    · exact half_B_bridge g
    · exact symmetric_direction_bridge g U hU hs

end
end Holant.Certificates.MatchingProductBridge
