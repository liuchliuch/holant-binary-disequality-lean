import Holant.Certificates.IcosahedralSeparator.Arithmetic
import Holant.Certificates.TetrahedralDeck.CardSemantics

/-! Exact integral encodings of eight times each bridge tensor. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def gsymmetric (j : Fin 15) (a b : Bool) : GScalar :=
  let v := icosahedralRaw (directionIndex j)
  if a = b then (v 0,if a then GoldenInt.neg (v 3) else v 3)
  else (GoldenInt.zero,v 1)

def regularCode (j : Fin 15) (x : Fin 4 → Bool) : GScalar :=
  gscale (if j.val < 3 then 4 else 1)
    (gmul (gsymmetric j (x 0) (x 3)) (gconj (gsymmetric j (x 1) (x 2))))

def candidateCode (i : Fin 18) (x : Fin 4 → Bool) : GScalar :=
  Fin.addCases (fun j : Fin 3 =>
    ![gz,gint (if x 0 = x 1 ∧ x 2 = x 3 then 4 else 0),
      gint (if x 0 = x 2 ∧ x 1 = x 3 then 4 else 0)] j) (fun j => regularCode j x) i

theorem gembed_gsymmetric (j : Fin 15) (a b : Bool) :
    gembed (gsymmetric j a b) = symmetricQuaternion (sliceVector j) a b := by
  cases a <;> cases b <;>
    simp [gembed,gsymmetric,symmetricQuaternion,sliceVector,Q0,Q1,Q3,Signature.equality]

theorem gembed_conj_gsymmetric (j : Fin 15) (a b : Bool) :
    gembed (gconj (gsymmetric j a b)) = conjugateQuaternion (sliceVector j) a b := by
  cases a <;> cases b <;>
    simp [gembed,gconj,gsymmetric,conjugateQuaternion,sliceVector,Q0,Q1,Q3,Signature.equality] <;> ring

theorem sliceVector_norm (j : Fin 15) : normSquare (sliceVector j) = if j.val < 3 then 1 else 4 := by
  fin_cases j <;>
    norm_num [normSquare,sliceVector,directionIndex,icosahedralRaw,GoldenInt.eval] <;>
    nlinarith [GoldenInt.golden_sq]

theorem gembed_regularCode (j : Fin 15) (x : Fin 4 → Bool) :
    gembed (regularCode j x) = 8*regular j x := by
  rw [regular_eq_R]
  unfold regularCode
  rw [gembed_scale,gembed_mul,gembed_gsymmetric,gembed_conj_gsymmetric]
  simp only [R,P2,inverseQuaternion,sliceVector_norm]
  split_ifs <;> norm_num <;> ring

theorem gembed_candidateCode (i : Fin 18) (x : Fin 4 → Bool) :
    gembed (candidateCode i x) = 8*candidate i x := by
  refine Fin.addCases (m := 3) (n := 15) (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · change gembed gz = 8*(0 : ℂ)
      simp
    · simp only [candidateCode,candidate,Fin.addCases_left,Matrix.cons_val_one,Matrix.cons_val_zero,gembed_int]
      simp [A,P0,Q0,Signature.equality,smul_eq_mul]
      split_ifs <;> norm_num at * <;> tauto
    · simp only [candidateCode,candidate,Fin.addCases_left,Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,gembed_int]
      simp [B,P1,Q0,Signature.equality,smul_eq_mul]
      split_ifs <;> norm_num at * <;> tauto
  · simpa only [candidateCode,candidate,Fin.addCases_right] using gembed_regularCode j x

theorem candidate_injective : Function.Injective candidate := by
  have hc : Function.Injective (fun i : Fin 18 => fun w : Fin 16 => candidateCode i (TetrahedralDeck.words w)) := by
    decide +kernel
  intro i j h
  apply hc
  funext w
  apply gembed_injective
  rw [gembed_candidateCode,gembed_candidateCode,h]

def bridgePoints : Finset FourTensor := by
  classical
  exact Finset.univ.image candidate

theorem bridgePoints_card : bridgePoints.card = 18 := by
  classical
  rw [bridgePoints,Finset.card_image_of_injective _ candidate_injective]
  simp

theorem mem_bridgePoints (W : FourTensor) : W ∈ bridgePoints ↔ bridgeConditions .icosahedral W := by
  classical
  rw [bridge_iff]
  simp [bridgePoints,eq_comm]

end
end Holant.Certificates.IcosahedralSeparator
