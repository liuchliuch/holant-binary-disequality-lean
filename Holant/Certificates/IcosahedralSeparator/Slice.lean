import Holant.Certificates.IcosahedralSeparator.Data

/-! The exact fifteen symmetric projective directions, including arbitrary
nonzero complex representatives. Completeness uses the literal group dictionary. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem directionIndex_injective : Function.Injective directionIndex := by decide +kernel

theorem symmetric_index_iff (k : Fin 60) :
    icosahedralRaw k 2 = GoldenInt.zero ↔ ∃ j : Fin 15, k = directionIndex j := by
  revert k
  decide +kernel

theorem representative_symmetric_iff (k : Fin 60) :
    transpose (representative .icosahedral k) = representative .icosahedral k ↔
      ∃ j : Fin 15, k = directionIndex j := by
  unfold representative raw goldenMatrix
  rw [quaternion_symmetric_iff,golden_eval_zero_iff,symmetric_index_iff]

theorem direction_symmetric (j : Fin 15) :
    transpose (representative .icosahedral (directionIndex j)) =
      representative .icosahedral (directionIndex j) :=
  (representative_symmetric_iff _).mpr ⟨j,rfl⟩

/-- This direction list is derived from all group members; no coverage premise
is imposed on the input complex matrix. -/
theorem symmetric_direction_iff (U : Binary) :
    groupDirection .icosahedral U ∧ transpose U = U ↔
      ∃ j : Fin 15, ∃ c : ℂ, c ≠ 0 ∧
        U = c • representative .icosahedral (directionIndex j) := by
  constructor
  · rintro ⟨hU,hS⟩
    obtain ⟨k,c,hc,rfl⟩ := (complete .icosahedral U).mp hU
    have hs : transpose (representative .icosahedral k) = representative .icosahedral k := by
      funext a b
      exact mul_left_cancel₀ hc (congrFun (congrFun hS a) b)
    obtain ⟨j,rfl⟩ := (representative_symmetric_iff k).mp hs
    exact ⟨j,c,hc,rfl⟩
  · rintro ⟨j,c,hc,rfl⟩
    refine ⟨groupDirection_smul _ (representative_mem _ _) hc,?_⟩
    change c • transpose (representative .icosahedral (directionIndex j)) = _
    rw [direction_symmetric]

theorem regular_bridge (j : Fin 15) : bridgeConditions .icosahedral (regular j) :=
  symmetric_direction_bridge _ _ (representative_mem _ _) (direction_symmetric j)

theorem candidate_bridge (i : Fin 18) : bridgeConditions .icosahedral (candidate i) := by
  refine Fin.addCases (m := 3) (n := 15) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · exact zero_bridge _
    · exact half_A_bridge _
    · exact half_B_bridge _
  · simpa only [candidate,Fin.addCases_right] using regular_bridge j

/-- Complete eighteen-candidate bridge classification with unrestricted complex
scales and all zero or cancellation cases inherited from the proved A.15. -/
theorem bridge_iff (W : FourTensor) :
    bridgeConditions .icosahedral W ↔ ∃ i : Fin 18, W = candidate i := by
  constructor
  · intro hW
    rcases (concrete_bridge_iff .icosahedral W).mp hW with h | h | h | ⟨U,hU,hS,h⟩
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
    · exact ⟨2,h⟩
    · obtain ⟨j,c,hc,he⟩ := (symmetric_direction_iff U).mp ⟨hU,hS⟩
      refine ⟨j.natAdd 3,?_⟩
      rw [h,he]
      have hs := matrixR_smul c hc (representative .icosahedral (directionIndex j))
        (representative_det_ne_zero .icosahedral (directionIndex j))
      simpa only [candidate,Fin.addCases_right,regular] using hs
  · rintro ⟨i,rfl⟩
    exact candidate_bridge i

theorem symmetricQuaternion_slice (j : Fin 15) :
    symmetricQuaternion (sliceVector j) = representative .icosahedral (directionIndex j) := by
  have hz := (symmetric_index_iff (directionIndex j)).mpr ⟨j,rfl⟩
  funext a b
  simp [symmetricQuaternion,sliceVector,representative,raw,goldenMatrix,quaternion,hz]

theorem sliceVector_ne_zero (j : Fin 15) : sliceVector j ≠ 0 := by
  intro hz
  have hq := symmetricQuaternion_slice j
  rw [hz] at hq
  apply representative_ne_zero .icosahedral (directionIndex j)
  rw [←hq]
  funext a b
  simp [symmetricQuaternion]

theorem regular_eq_R (j : Fin 15) : regular j = R (sliceVector j) := by
  rw [regular,←symmetricQuaternion_slice,matrixR_symmetricQuaternion _ (sliceVector_ne_zero j)]

end
end Holant.Certificates.IcosahedralSeparator
