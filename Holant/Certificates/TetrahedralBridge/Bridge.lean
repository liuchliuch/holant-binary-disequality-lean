import Holant.Certificates.TetrahedralOrientation.Data

/-! Complete specialization of the proved A.15 bridge to the literal tetrahedral
group. Arbitrary complex scales and every cancellation case remain included. -/
namespace Holant.Certificates.TetrahedralBridge
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def axisIndex : Fin 3 → Fin 4 := ![0,1,3]
def regular (j : Fin 3) : FourTensor := TetrahedralOrientation.axisR (axisIndex j)
def candidate : Fin 6 → FourTensor := ![0,(1/2 : ℂ) • A,(1/2 : ℂ) • B,regular 0,regular 1,regular 2]

theorem symmetric_direction_axes (U : Binary) (hU : groupDirection .tetrahedral U)
    (hS : transpose U = U) : ∃ c : ℂ, c ≠ 0 ∧ ∃ j : Fin 3, U = c • quaternionBasis (axisIndex j) := by
  rcases hU with ⟨c,hc,V,hV,rfl⟩
  have hs : transpose V = V := by
    funext a b
    apply mul_left_cancel₀ hc
    exact congrFun (congrFun hS a) b
  rcases hV with ⟨k,rfl⟩ | ⟨ε,rfl⟩
  · fin_cases k
    · exact ⟨c,hc,0,rfl⟩
    · exact ⟨c,hc,1,rfl⟩
    · have he := congrFun (congrFun hs false) true
      norm_num [transpose,quaternionBasis,Q2] at he
    · exact ⟨c,hc,2,rfl⟩
  · have he := (quaternion_symmetric_iff _).mp hs
    exact False.elim (signBit_ne_zero (ε 1) he)

def unitAxis (j : Fin 3) : Fin 3 → ℝ := fun k => if k = j then 1 else 0

theorem unitAxis_ne_zero (j : Fin 3) : unitAxis j ≠ 0 := by
  intro h
  have he := congrFun h j
  simp [unitAxis] at he

theorem quaternion_unitAxis (j : Fin 3) : symmetricQuaternion (unitAxis j) = quaternionBasis (axisIndex j) := by
  fin_cases j <;> funext a b <;> simp [symmetricQuaternion,unitAxis,quaternionBasis,axisIndex]

theorem matrixR_axis (j : Fin 3) : matrixR (quaternionBasis (axisIndex j)) = regular j := by
  rw [← quaternion_unitAxis,matrixR_symmetricQuaternion _ (unitAxis_ne_zero j)]
  fin_cases j <;> funext x <;>
    simp [R,inverseQuaternion,conjugateQuaternion,symmetricQuaternion,normSquare,unitAxis,
      regular,axisIndex,TetrahedralOrientation.axisR,P2,smul_eq_mul] <;> ring

theorem axis_symmetric (j : Fin 3) : transpose (quaternionBasis (axisIndex j)) = quaternionBasis (axisIndex j) := by
  fin_cases j <;> funext a b <;> cases a <;> cases b <;> rfl

theorem regular_bridge (j : Fin 3) : bridgeConditions .tetrahedral (regular j) := by
  rw [← matrixR_axis]
  exact symmetric_direction_bridge _ _ (quaternion_axis_direction _ _) (axis_symmetric j)

theorem candidate_bridge (i : Fin 6) : bridgeConditions .tetrahedral (candidate i) := by
  fin_cases i
  · exact zero_bridge _
  · exact half_A_bridge _
  · exact half_B_bridge _
  · exact regular_bridge 0
  · exact regular_bridge 1
  · exact regular_bridge 2

/-- Exact six-point simultaneous solution set, derived from full complex A.15. -/
theorem bridge_iff (W : FourTensor) : bridgeConditions .tetrahedral W ↔ ∃ i : Fin 6, W = candidate i := by
  constructor
  · intro hW
    rcases (concrete_bridge_iff .tetrahedral W).mp hW with h | h | h | ⟨U,hU,hS,h⟩
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · obtain ⟨c,hc,j,he⟩ := symmetric_direction_axes U hU hS
      refine ⟨j.natAdd 3,?_⟩
      rw [h,he,matrixR_smul c hc _ (groupDirection_det_ne_zero _ (quaternion_axis_direction .tetrahedral _)),matrixR_axis]
      fin_cases j <;> rfl
  · rintro ⟨i,rfl⟩
    exact candidate_bridge i

end
end Holant.Certificates.TetrahedralBridge
