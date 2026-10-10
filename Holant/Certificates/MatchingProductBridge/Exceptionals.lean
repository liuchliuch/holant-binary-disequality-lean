import Holant.Certificates.MatchingProductBridge.PlatonicModels

/-! The three exceptional bridge vectors satisfy the literal T/O/I cone tests,
using actual quaternion axes and nonzero representative scalars. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section

theorem X_direction (g : PlatonicModel) : groupDirection g X := by
  have h := groupDirection_smul g (quaternion_axis_direction g 1)
    (neg_ne_zero.mpr Complex.I_ne_zero)
  have he : (-Complex.I) • quaternionBasis 1 = X := by
    funext a b
    cases a <;> cases b <;> norm_num [quaternionBasis,X,Q1,Holant.Signature.disequality,smul_eq_mul]
  rwa [he] at h

theorem Q0_X_direction (g : PlatonicModel) : groupDirection g (multiply Q0 X) := by
  have he : multiply Q0 X = X := by
    funext a b
    cases a <;> cases b <;> simp [multiply,Q0,X,Holant.Signature.equality,Holant.Signature.disequality]
  rw [he]
  exact X_direction g

theorem Q2_X_direction (g : PlatonicModel) : groupDirection g (multiply Q2 X) := by
  have h := groupDirection_smul g (quaternion_axis_direction g 3)
    (neg_ne_zero.mpr Complex.I_ne_zero)
  have he : (-Complex.I) • quaternionBasis 3 = multiply Q2 X := by
    funext a b
    cases a <;> cases b <;> norm_num [quaternionBasis,Q3,Q2,X,multiply,Holant.Signature.disequality,smul_eq_mul]
  rwa [he] at h

theorem A_mem_cone (g : PlatonicModel) : matchingCone g A :=
  Or.inr ⟨0,Q0,Q0,Q0_X_direction g,Q0_X_direction g,1,one_ne_zero,by simp [matchingProduct,A]⟩

theorem B_mem_cone (g : PlatonicModel) : matchingCone g B :=
  Or.inr ⟨1,Q0,Q0,Q0_X_direction g,Q0_X_direction g,1,one_ne_zero,by simp [matchingProduct,B]⟩

theorem C_mem_cone (g : PlatonicModel) : matchingCone g C :=
  Or.inr ⟨2,Q2,Q2,Q2_X_direction g,Q2_X_direction g,1,one_ne_zero,by simp [matchingProduct,C]⟩

theorem zero_bridge (g : PlatonicModel) : bridgeConditions g 0 := by
  refine ⟨matchingCone_zero g,?_,?_⟩
  · simpa using A_mem_cone g
  · simpa using matchingCone_smul g (B_mem_cone g) (-1)

theorem half_A_bridge (g : PlatonicModel) : bridgeConditions g ((1/2 : ℂ) • A) := by
  have h2 : (2 : ℂ) • ((1/2 : ℂ) • A) = A := by rw [smul_smul]; norm_num
  refine ⟨matchingCone_smul g (A_mem_cone g) _,?_,?_⟩
  · rw [h2,sub_self]
    exact matchingCone_zero g
  · rw [h2,A_sub_B]
    exact C_mem_cone g

theorem half_B_bridge (g : PlatonicModel) : bridgeConditions g ((1/2 : ℂ) • B) := by
  have h2 : (2 : ℂ) • ((1/2 : ℂ) • B) = B := by rw [smul_smul]; norm_num
  refine ⟨matchingCone_smul g (B_mem_cone g) _,?_,?_⟩
  · rw [h2,A_sub_B]
    exact C_mem_cone g
  · rw [h2,sub_self]
    exact matchingCone_zero g

theorem exceptional_triple_sum :
    (0 : FourTensor) + (1/2 : ℂ) • A + (1/2 : ℂ) • B = (fun x => (A x+B x)/2) := by
  funext x
  simp [smul_eq_mul]
  ring

end
end Holant.Certificates.MatchingProductBridge
