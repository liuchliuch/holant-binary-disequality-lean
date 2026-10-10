import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureClosedMinimal

/-! Proper Affine coordinate faces force the rank-three cubic obstruction
 to be a sign, without an Affine-square assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeCore
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeAffineThreeFaces
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option Elab.async false

/-- The one full coordinate cube keeps all eight actual coefficient values. -/
def cubicRatio (u : Signature AlgebraicComplex 3) : AlgebraicComplex :=
  (u ![true,true,true]*u ![true,false,false]*u ![false,true,false]*u ![false,false,true])/
  (u ![true,true,false]*u ![true,false,true]*u ![false,true,true]*u ![false,false,false])

def value (u : Signature AlgebraicComplex 3) (a b c : Bool) : AlgebraicComplex := u ![a,b,c]

theorem eval_value (u : Signature AlgebraicComplex 3) (x : Word 3) :
    u x=value u (x 0) (x 1) (x 2) := by
  congr 1
  funext i
  fin_cases i <;> rfl

/-- A translated coordinate cube is the same eight coefficients, with the
numerator and denominator interchanged exactly at odd base parity. -/
theorem distinct_cube_ratio (u : Signature AlgebraicComplex 3) (z : Word 3)
    (i j k : Fin 3) (distinct : i≠j ∧ i≠k ∧ j≠k) :
    thirdRatio u z (basis i) (basis j) (basis k)=
      if (z 0^^z 1)^^z 2 then (cubicRatio u)⁻¹ else cubicRatio u := by
  simp only [thirdRatio,cubicRatio,eval_value u]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at distinct
  all_goals cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;>
    simp [AffinePhase.xor,basis,h0,h1,h2,div_eq_mul_inv,mul_inv_rev,value] <;> ring

theorem origin_cube_ratio (u : Signature AlgebraicComplex 3) :
    thirdRatio u (origin 3) (basis 0) (basis 1) (basis 2)=cubicRatio u := by
  rw [distinct_cube_ratio u (origin 3) 0 1 2 (by decide)]
  rfl

theorem thirdRatio_square {n : ℕ} (u : Signature AlgebraicComplex n) (z a b c : Word n) :
    thirdRatio (fun x=>u x^2) z a b c=(thirdRatio u z a b c)^2 := by
  simp only [thirdRatio,div_pow,mul_pow]

theorem thirdRatio_mul {n : ℕ} (u v : Signature AlgebraicComplex n) (z a b c : Word n) :
    thirdRatio (fun x=>u x*v x) z a b c=thirdRatio u z a b c*thirdRatio v z a b c := by
  simp only [thirdRatio,div_eq_mul_inv,mul_inv_rev]
  ring


def phaseSeven : Signature AlgebraicComplex 3:=fun x=>if x 0 || x 1 || x 2 then -1 else 1

theorem phaseSeven_full (x : Word 3) : phaseSeven x≠0:=by
  unfold phaseSeven
  split_ifs <;> norm_num

theorem phaseSeven_square (x : Word 3) : phaseSeven x*phaseSeven x=1:=by
  unfold phaseSeven
  split_ifs <;> norm_num

theorem phaseSeven_cubes (z : Word 3) (i j k : Fin 3) :
    thirdRatio phaseSeven z (basis i) (basis j) (basis k)=
      if i≠j ∧ i≠k ∧ j≠k then -1 else 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals cases h0:z 0 <;> cases h1:z 1 <;> cases h2:z 2 <;>
    norm_num [thirdRatio,phaseSeven,AffinePhase.xor,basis,h0,h1,h2]

variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3 → ∀z : Word 3,Affine (minor D S z))

include minimal in
theorem repeated_cube (z : Word 3) (i j k : Fin 3) (repeated : ¬(i≠j ∧ i≠k ∧ j≠k)) :
    thirdRatio D.reduced z (basis i) (basis j) (basis k)=1 := by
  have small : ({i,j,k} : Finset (Fin 3)).card<3 := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals try { norm_num at repeated }
    all_goals norm_num
  exact cube_of_affine_face D.reduced D.reduced_full z i j k
    (face_affine_of_minor D {i,j,k} z (minimal {i,j,k} small z))


include minimal in
theorem cubicRatio_square : cubicRatio D.reduced^2=1 := by
  have h0:=(thirdRatio_eq_one_iff D.reduced_full (origin 3) (basis 0) (basis 1) (basis 1)).mp
    (repeated_cube D minimal (origin 3) 0 1 1 (by simp))
  have h1:=(thirdRatio_eq_one_iff D.reduced_full ![false,false,true] (basis 0) (basis 1) (basis 1)).mp
    (repeated_cube D minimal ![false,false,true] 0 1 1 (by simp))
  simp only [eval_value D.reduced] at h0 h1
  norm_num [AffinePhase.xor,basis,origin,value] at h0 h1
  unfold cubicRatio
  rw [div_pow]
  apply (div_eq_one_iff_eq (pow_ne_zero 2 (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (D.reduced_full _) (D.reduced_full _))
      (D.reduced_full _)) (D.reduced_full _)))).mpr
  linear_combination (D.reduced ![true,true,true]*D.reduced ![false,false,true])^2*h0 -
    (D.reduced ![true,true,false]*D.reduced ![false,false,false])^2*h1

include minimal in
theorem cubicRatio_ne_one (bad : ¬Affine f) : cubicRatio D.reduced≠1 := by
  intro equal
  apply NoIPureClosedMinimal.nonAffine_reduced D bad
  apply affine_of_coordinate_cubes D.reduced D.reduced_full
  intro z i j k
  by_cases distinct:i≠j ∧ i≠k ∧ j≠k
  · rw [distinct_cube_ratio _ _ _ _ _ distinct,equal]
    split_ifs <;> simp
  · exact repeated_cube D minimal z i j k distinct

include minimal in
theorem cubicRatio_negative (bad : ¬Affine f) : cubicRatio D.reduced= -1 :=
  (sq_eq_one_iff.mp (cubicRatio_square D minimal)).resolve_left (cubicRatio_ne_one D minimal bad)

include minimal in
theorem phaseSeven_affine (bad : ¬Affine f) : Affine (fun x=>phaseSeven x*D.reduced x) := by
  have neg:=cubicRatio_negative D minimal bad
  apply affine_of_coordinate_cubes (fun x=>phaseSeven x*D.reduced x)
    (fun x=>mul_ne_zero (phaseSeven_full x) (D.reduced_full x))
  intro z i j k
  rw [thirdRatio_mul,phaseSeven_cubes]
  by_cases distinct:i≠j ∧ i≠k ∧ j≠k
  · rw [ite_eq_left distinct,distinct_cube_ratio _ _ _ _ _ distinct,neg]
    split_ifs <;> norm_num
  · rw [ite_eq_right distinct,repeated_cube D minimal z i j k distinct,one_mul]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeCore
end
