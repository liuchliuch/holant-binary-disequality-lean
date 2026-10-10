import Holant.Certificates.IcosahedralSeparator.TensorCode

/-! The five literal manuscript frames and exact orthogonality graph. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def frameScale (j : Fin 15) : ℝ := if j.val < 3 then 1 else sliceVector j 0

theorem sliceVector_eq_sourceFrame (j : Fin 15) :
    sliceVector j = frameScale j • sourceFrame j := by
  funext k
  fin_cases j <;> fin_cases k <;>
    norm_num [sliceVector,frameScale,sourceFrame,directionIndex,icosahedralRaw,
      GoldenInt.eval,GoldenInt.reciprocal_eq,smul_eq_mul] <;>
    nlinarith [GoldenInt.golden_sq]

theorem frameScale_ne_zero (j : Fin 15) : frameScale j ≠ 0 := by
  intro h
  have he := sliceVector_eq_sourceFrame j
  rw [h,zero_smul] at he
  exact sliceVector_ne_zero j he

theorem sourceFrame_ne_zero (j : Fin 15) : sourceFrame j ≠ 0 := by
  intro h
  have he := sliceVector_eq_sourceFrame j
  rw [h,smul_zero] at he
  exact sliceVector_ne_zero j he

theorem R_real_smul (c : ℝ) (hc : c ≠ 0) (u : Fin 3 → ℝ) (hu : u ≠ 0) :
    R (c • u) = R u := by
  have hn : (normSquare u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (normSquare_pos u hu))
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hs : normSquare (c • u) = c^2*normSquare u := by
    simp [normSquare,smul_eq_mul]; ring
  funext x
  simp only [R,P2,inverseQuaternion,hs,Complex.ofReal_mul,Complex.ofReal_pow,
    symmetricQuaternion,conjugateQuaternion,Pi.smul_apply,smul_eq_mul]
  push_cast
  field_simp
  <;> ring

theorem regular_eq_sourceFrame (j : Fin 15) : regular j = R (sourceFrame j) := by
  rw [regular_eq_R,sliceVector_eq_sourceFrame,R_real_smul _ (frameScale_ne_zero j) _ (sourceFrame_ne_zero j)]

def dotCode (j k : Fin 15) : GoldenInt :=
  let v := icosahedralRaw (directionIndex j)
  let w := icosahedralRaw (directionIndex k)
  GoldenInt.add (GoldenInt.add (GoldenInt.mul (v 0) (w 0)) (GoldenInt.mul (v 1) (w 1)))
    (GoldenInt.mul (v 3) (w 3))

theorem eval_dotCode (j k : Fin 15) : GoldenInt.eval (dotCode j k) = dot (sliceVector j) (sliceVector k) := by
  simp [dotCode,dot,sliceVector,Fin.sum_univ_succ]
  ring

theorem dotCode_zero_iff : ∀ j k : Fin 15,
    dotCode j k = GoldenInt.zero ↔ j.val/3 = k.val/3 ∧ j ≠ k := by decide +kernel

/-- Each of the fifteen directions is orthogonal to exactly its two partners
in the same displayed frame. -/
theorem slice_orthogonal_iff (j k : Fin 15) :
    dot (sliceVector j) (sliceVector k) = 0 ↔ j.val/3 = k.val/3 ∧ j ≠ k := by
  rw [←eval_dotCode,golden_eval_zero_iff,dotCode_zero_iff]

theorem sourceFrame_orthogonal_iff (j k : Fin 15) :
    dot (sourceFrame j) (sourceFrame k) = 0 ↔ j.val/3 = k.val/3 ∧ j ≠ k := by
  rw [←slice_orthogonal_iff]
  have he : dot (sliceVector j) (sliceVector k) =
      (frameScale j*frameScale k)*dot (sourceFrame j) (sourceFrame k) := by
    rw [sliceVector_eq_sourceFrame,sliceVector_eq_sourceFrame]
    simp [dot,smul_eq_mul,Fin.sum_univ_succ]
    ring
  rw [he,mul_eq_zero]
  simp [frameScale_ne_zero]

end
end Holant.Certificates.IcosahedralSeparator
