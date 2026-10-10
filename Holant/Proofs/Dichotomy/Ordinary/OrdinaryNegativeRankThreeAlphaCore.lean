import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseUniformMinimal
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingAlpha

/-! The rank-three minimal residual has precisely the nontrivial cubic sign.
Its product with the actual seven-character uniform phase is Affine. Every
proper coordinate face is used with its real outside assignment. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankThreeAlphaCore
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open OrdinaryNegativeAffineThreeFaces
namespace A
export OrdinaryNegativeSparseMixingAlpha (phaseSeven phaseSeven_formula twist_nonzero codeSeven)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
open scoped BigOperators

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

theorem phaseSeven_cubes (z : Word 3) (i j k : Fin 3) :
    thirdRatio A.phaseSeven z (basis i) (basis j) (basis k)=
      if i≠j ∧ i≠k ∧ j≠k then -1 else 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals cases h0 : z 0 <;> cases h1 : z 1 <;> cases h2 : z 2 <;>
    norm_num [thirdRatio,A.phaseSeven_formula,AffinePhase.xor,basis,h0,h1,h2]

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
theorem cubicRatio_ne_one (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) : cubicRatio D.reduced≠1 := by
  intro equal
  apply D.nonAffine_reduced square nonzero bad
  apply affine_of_coordinate_cubes D.reduced D.reduced_full
  intro z i j k
  by_cases distinct : i≠j ∧ i≠k ∧ j≠k
  · rw [distinct_cube_ratio _ _ _ _ _ distinct,equal]
    split_ifs <;> simp
  · exact repeated_cube D minimal z i j k distinct

include minimal in
theorem cubicRatio_negative (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) : cubicRatio D.reduced= -1 := by
  have hs : Affine (fun x=>D.reduced x^2) := square.precompose D.encode D.affine
  have hfull : ∀x,D.reduced x^2≠0 := fun x=>pow_ne_zero 2 (D.reduced_full x)
  have h := thirdTrivial_of_affine hfull hs (origin 3) (basis 0) (basis 1) (basis 2)
  rw [thirdRatio_square,origin_cube_ratio] at h
  exact (sq_eq_one_iff.mp h).resolve_left (cubicRatio_ne_one D minimal square nonzero bad)

include minimal in
/-- The sole nontrivial cubic sign is canceled by the seven-character phase;
all repeated-direction conditions already come from genuine proper faces. -/
theorem minimal_phaseSeven_affine (square : Affine (fun x=>f x^2)) (nonzero : f≠0)
    (bad : ¬Affine f) : Affine (fun x=>A.phaseSeven x*D.reduced x) := by
  have neg := cubicRatio_negative D minimal square nonzero bad
  apply affine_of_coordinate_cubes (fun x=>A.phaseSeven x*D.reduced x)
    (fun x=>mul_ne_zero (A.twist_nonzero (A.codeSeven x)) (D.reduced_full x))
  intro z i j k
  rw [thirdRatio_mul,phaseSeven_cubes]
  by_cases distinct : i≠j ∧ i≠k ∧ j≠k
  · rw [ite_eq_left distinct,distinct_cube_ratio _ _ _ _ _ distinct,neg]
    split_ifs <;> norm_num
  · rw [ite_eq_right distinct,repeated_cube D minimal z i j k distinct,one_mul]

/-- The complementary uniform-class row has the same cubic residual,
using the exact original-pin scalar equivalence on every proper face. -/
theorem uniform_minimal_phaseSeven_affine (square : Affine (fun x=>f x^2))
    (bad : ¬Affine (OrdinaryNegativeAffineRankOne.uniform f))
    (minimalUniform : ∀S : Finset (Fin 3),S.card<3 → ∀z : Word 3,
      Affine (OrdinaryNegativeAffineRankOne.uniform (minor D S z))) :
    Affine (fun x=>A.phaseSeven x*OrdinaryNegativeAffineRankOne.uniform f (D.encode x)) := by
  let E := OrdinaryNegativeSparseUniformMinimal.uniformChart D
  have hn : OrdinaryNegativeAffineRankOne.uniform f≠0 := by
    intro hz
    exact E.supported (origin 3) (congrFun hz _)
  exact minimal_phaseSeven_affine E
    (fun S hS z=>(OrdinaryNegativeSparseUniformMinimal.uniform_minor_affine_iff D S z).mpr (minimalUniform S hS z))
    (OrdinaryNegativeAffineRankOne.uniform_square f square) hn bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankThreeAlphaCore
end
