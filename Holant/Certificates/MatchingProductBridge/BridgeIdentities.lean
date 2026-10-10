import Holant.Certificates.MatchingProductBridge.Tensors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Exact unscaled matching-product bridge identities. These prove the constructive
symmetric-matrix branch; completeness of the three Platonic matching cones is separate. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section

/-- The first source bridge difference is a literal matching1 product. -/
theorem bridge_first (U V : Binary) (hUV : multiply U (transpose V) = Q0) :
    A - P2 U V = P1 (multiply U Q2) (multiply V Q2) := by
  funext x
  have h (a b : Bool) : U a false * V b false + U a true * V b true = Q0 a b :=
    congrFun (congrFun hUV a) b
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  simp only [Q0,Holant.Signature.equality,ite_true,Bool.false_eq_true,Bool.true_eq_false,ite_false] at h00 h01 h10 h11
  rcases hx : x 0 with _ | _ <;> rcases hy : x 1 with _ | _ <;>
    rcases hz : x 2 with _ | _ <;> rcases hw : x 3 with _ | _ <;>
    simp [A,P0,P1,P2,multiply,Q0,Q2,Holant.Signature.equality,hx,hy,hz,hw] <;>
    first | (solve | ring) | (solve | linear_combination -h00) | (solve | linear_combination -h01) |
      (solve | linear_combination -h10) | (solve | linear_combination -h11)

/-- Symmetry gives the second source difference as a literal matching0 product. -/
theorem bridge_second (U V : Binary) (hUV : multiply U (transpose V) = Q0)
    (hV : transpose V = V) :
    P2 U V - B = -P0 (multiply U Q2) (multiply V Q2) := by
  funext x
  have h := congrFun (bridge_first U V hUV) ![x 0,x 2,x 1,x 3]
  have hs : V (x 2) (x 1) = V (x 1) (x 2) := congrFun (congrFun hV (x 1)) (x 2)
  change Q0 (x 0) (x 2) * Q0 (x 1) (x 3) - U (x 0) (x 3) * V (x 2) (x 1) =
    multiply U Q2 (x 0) (x 1) * multiply V Q2 (x 2) (x 3) at h
  rw [hs] at h
  change U (x 0) (x 3) * V (x 1) (x 2) - Q0 (x 0) (x 2) * Q0 (x 1) (x 3) =
    -(multiply U Q2 (x 0) (x 1) * multiply V Q2 (x 2) (x 3))
  linear_combination -h

theorem normSquare_pos (u : Fin 3 → ℝ) (hu : u ≠ 0) : 0 < normSquare u := by
  have h0 := sq_nonneg (u 0)
  have h1 := sq_nonneg (u 1)
  have h2 := sq_nonneg (u 2)
  by_contra hn
  have hn' : normSquare u ≤ 0 := le_of_not_gt hn
  unfold normSquare at hn'
  have e0 : (u 0)^2 = 0 := by linarith
  have e1 : (u 1)^2 = 0 := by linarith
  have e2 : (u 2)^2 = 0 := by linarith
  have z0 : u 0 = 0 := sq_eq_zero_iff.mp e0
  have z1 : u 1 = 0 := sq_eq_zero_iff.mp e1
  have z2 : u 2 = 0 := sq_eq_zero_iff.mp e2
  apply hu
  funext i
  fin_cases i
  · exact z0
  · exact z1
  · exact z2

def inverseQuaternion (u : Fin 3 → ℝ) : Binary :=
  fun a b => (normSquare u : ℂ)⁻¹ * conjugateQuaternion u a b

theorem quaternion_inverse (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    multiply (symmetricQuaternion u) (inverseQuaternion u) = Q0 := by
  have hn : (normSquare u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (normSquare_pos u hu))
  funext a b
  have h := congrFun (congrFun (quaternion_mul_conjugate u) a) b
  dsimp only [multiply] at h
  dsimp only [multiply,inverseQuaternion]
  calc
    _ = (normSquare u : ℂ)⁻¹ *
      (symmetricQuaternion u a false * conjugateQuaternion u false b +
        symmetricQuaternion u a true * conjugateQuaternion u true b) := by ring
    _ = _ := by rw [h]; simp [hn]

theorem inverseQuaternion_symmetric (u : Fin 3 → ℝ) : transpose (inverseQuaternion u) = inverseQuaternion u := by
  funext a b
  cases a <;> cases b <;>
    simp [transpose,inverseQuaternion,conjugateQuaternion,Q0,Q1,Q3,Holant.Signature.equality]

/-- The normalized R vector carries its exact scalar1/2. -/
def R (u : Fin 3 → ℝ) : FourTensor := fun x => (1/2 : ℂ) * P2 (symmetricQuaternion u) (inverseQuaternion u) x

theorem symmetric_bridge_first (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    A - (2 : ℂ) • R u = P1 (multiply (symmetricQuaternion u) Q2) (multiply (inverseQuaternion u) Q2) := by
  have h := bridge_first (symmetricQuaternion u) (inverseQuaternion u) (by
    rw [inverseQuaternion_symmetric]; exact quaternion_inverse u hu)
  convert h using 1
  funext x
  simp [R,smul_eq_mul]

theorem symmetric_bridge_second (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    (2 : ℂ) • R u - B = -P0 (multiply (symmetricQuaternion u) Q2) (multiply (inverseQuaternion u) Q2) := by
  have h := bridge_second (symmetricQuaternion u) (inverseQuaternion u) (by
    rw [inverseQuaternion_symmetric]; exact quaternion_inverse u hu) (inverseQuaternion_symmetric u)
  convert h using 1
  funext x
  simp [R,smul_eq_mul]

end
end Holant.Certificates.MatchingProductBridge
