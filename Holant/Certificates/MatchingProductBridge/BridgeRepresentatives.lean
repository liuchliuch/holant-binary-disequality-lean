import Holant.Certificates.MatchingProductBridge.ConcreteConverse

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem binaryInverse_smul (c : ℂ) (hc : c ≠ 0) (U : Binary)
    (hU : Matrix.det (Matrix.of U) ≠ 0) : binaryInverse (c • U) = c⁻¹ • binaryInverse U := by
  have h : (c • Matrix.of U) * (c⁻¹ • (Matrix.of U)⁻¹) = (1 : Matrix Bool Bool ℂ) := by
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hU)]
    simp [hc]
  have he := Matrix.inv_eq_right_inv h
  exact congrArg (fun M : Matrix Bool Bool ℂ => fun a b => M a b) he

theorem binaryInverseTranspose_smul (c : ℂ) (hc : c ≠ 0) (U : Binary)
    (hU : Matrix.det (Matrix.of U) ≠ 0) : binaryInverseTranspose (c • U) = c⁻¹ • binaryInverseTranspose U := by
  unfold binaryInverseTranspose
  rw [binaryInverse_smul c hc U hU]
  rfl

/-- The bridge vector is independent of the nonzero representative scale. -/
theorem matrixR_smul (c : ℂ) (hc : c ≠ 0) (U : Binary)
    (hU : Matrix.det (Matrix.of U) ≠ 0) : matrixR (c • U) = matrixR U := by
  rw [matrixR,binaryInverseTranspose_smul c hc U hU]
  funext x
  simp [matrixR,P2,smul_eq_mul]
  field_simp [hc]

theorem binaryInverse_symmetricQuaternion (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    binaryInverse (symmetricQuaternion u) = inverseQuaternion u := by
  have h : Matrix.of (symmetricQuaternion u) * Matrix.of (inverseQuaternion u) = 1 := by
    rw [← multiply_eq_matrix_mul,quaternion_inverse u hu]
    exact Q0_eq_matrix_one
  have he := Matrix.inv_eq_right_inv h
  exact congrArg (fun M : Matrix Bool Bool ℂ => fun a b => M a b) he

theorem matrixR_symmetricQuaternion (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    matrixR (symmetricQuaternion u) = R u := by
  unfold matrixR binaryInverseTranspose
  rw [binaryInverse_symmetricQuaternion u hu,inverseQuaternion_symmetric]
  rfl

/-- Every symmetric group-direction bridge has the asserted nonzero real representative. -/
theorem matrixR_group_representative (g : PlatonicModel) (U : Binary)
    (hU : groupDirection g U) (hS : transpose U = U) :
    ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ groupDirection g (symmetricQuaternion u) ∧ matrixR U = R u := by
  rcases groupDirection_symmetric_rep g hU hS with ⟨c,hc,u,hu,he⟩
  have hg := groupDirection_smul g hU (inv_ne_zero hc)
  rw [he,smul_smul,inv_mul_cancel₀ hc,one_smul] at hg
  refine ⟨u,hu,hg,?_⟩
  rw [he,matrixR_smul c hc _ (groupDirection_det_ne_zero g hg),matrixR_symmetricQuaternion u hu]

/-- Exact real-coordinate form of the complete concrete bridge classification. -/
theorem concrete_bridge_real_iff (g : PlatonicModel) (W : FourTensor) :
    bridgeConditions g W ↔
      W = 0 ∨ W = (1/2 : ℂ) • A ∨ W = (1/2 : ℂ) • B ∨
        ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ groupDirection g (symmetricQuaternion u) ∧ W = R u := by
  rw [concrete_bridge_iff]
  constructor
  · rintro (h | h | h | ⟨U,hU,hS,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (matrixR_group_representative g U hU hS)))
  · rintro (h | h | h | ⟨u,hu,hg,rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr ⟨symmetricQuaternion u,hg,symmetricQuaternion_transpose u,
        (matrixR_symmetricQuaternion u hu).symm⟩))

end
end Holant.Certificates.MatchingProductBridge
