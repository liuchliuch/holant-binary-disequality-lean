import Holant.Certificates.MatchingProductBridge.GroupInverses

/-! Integer arithmetic for actual golden-ratio quaternion representatives. -/
namespace Holant.Certificates.RainbowOrbit
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000

structure GoldenInt where
  a : ℤ
  b : ℤ
  deriving DecidableEq

namespace GoldenInt

def zero : GoldenInt := ⟨0,0⟩
def ofInt (n : ℤ) : GoldenInt := ⟨n,0⟩
def add (u v : GoldenInt) : GoldenInt := ⟨u.a+v.a,u.b+v.b⟩
def neg (u : GoldenInt) : GoldenInt := ⟨-u.a,-u.b⟩
def sub (u v : GoldenInt) : GoldenInt := add u (neg v)
def mul (u v : GoldenInt) : GoldenInt :=
  ⟨u.a*v.a+u.b*v.b,u.a*v.b+u.b*v.a+u.b*v.b⟩
def norm (u : GoldenInt) : ℤ := u.a^2+u.a*u.b-u.b^2
noncomputable def eval (u : GoldenInt) : ℝ := u.a+u.b*goldenRatio

theorem golden_sq : goldenRatio^2 = goldenRatio+1 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  dsimp [goldenRatio]
  nlinarith

theorem golden_ne_zero : goldenRatio ≠ 0 := by
  intro h
  have hh := golden_sq
  rw [h] at hh
  norm_num at hh

theorem reciprocal_eq : goldenReciprocal = goldenRatio-1 := by
  dsimp [goldenReciprocal]
  apply inv_eq_of_mul_eq_one_left
  nlinarith [golden_sq]

@[simp] theorem eval_zero : eval zero = 0 := by simp [eval,zero]
@[simp] theorem eval_ofInt (n : ℤ) : eval (ofInt n) = n := by simp [eval,ofInt]
@[simp] theorem eval_add (u v : GoldenInt) : eval (add u v) = eval u+eval v := by
  simp [eval,add]
  ring
@[simp] theorem eval_neg (u : GoldenInt) : eval (neg u) = -eval u := by
  simp [eval,neg]
  ring
@[simp] theorem eval_sub (u v : GoldenInt) : eval (sub u v) = eval u-eval v := by
  simp [sub,sub_eq_add_neg]
@[simp] theorem eval_mul (u v : GoldenInt) : eval (mul u v) = eval u*eval v := by
  simp only [eval,mul,Int.cast_add,Int.cast_mul]
  ring_nf
  rw [golden_sq]
  ring

theorem norm_identity (u : GoldenInt) :
    (norm u : ℝ) = eval u*(u.a+u.b*(1-goldenRatio)) := by
  simp only [norm,eval,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_pow]
  nlinarith [golden_sq]

theorem eval_ne_zero (u : GoldenInt) (h : norm u ≠ 0) : eval u ≠ 0 := by
  intro hz
  have hh := norm_identity u
  rw [hz,zero_mul] at hh
  exact h (Int.cast_eq_zero.mp hh)

end GoldenInt

abbrev GoldenVector := Fin 4 → GoldenInt

def goldenQuaternionProduct (u v : GoldenVector) : GoldenVector :=
  let m := GoldenInt.mul
  let a := GoldenInt.add
  let s := GoldenInt.sub
  ![s (s (s (m (u 0) (v 0)) (m (u 1) (v 1))) (m (u 2) (v 2))) (m (u 3) (v 3)),
    a (s (a (m (u 0) (v 1)) (m (u 1) (v 0))) (m (u 2) (v 3))) (m (u 3) (v 2)),
    a (s (a (m (u 0) (v 2)) (m (u 2) (v 0))) (m (u 3) (v 1))) (m (u 1) (v 3)),
    a (s (a (m (u 0) (v 3)) (m (u 3) (v 0))) (m (u 1) (v 2))) (m (u 2) (v 1))]

def goldenScale (c : ℤ) (u : GoldenVector) : GoldenVector :=
  fun i => GoldenInt.mul (GoldenInt.ofInt c) (u i)

noncomputable def goldenMatrix (u : GoldenVector) : Matrix Bool Bool ℂ :=
  quaternion (fun i => GoldenInt.eval (u i))

theorem goldenMatrix_scale (c : ℤ) (u : GoldenVector) :
    goldenMatrix (goldenScale c u) = (c : ℂ) • goldenMatrix u := by
  unfold goldenMatrix goldenScale
  simp only [GoldenInt.eval_mul,GoldenInt.eval_ofInt]
  exact quaternion_real_smul (c : ℝ) (fun i => GoldenInt.eval (u i))

theorem goldenMatrix_product (u v : GoldenVector) :
    goldenMatrix (goldenQuaternionProduct u v) = goldenMatrix u * goldenMatrix v := by
  ext a b
  cases a <;> cases b <;>
    simp [goldenMatrix,goldenQuaternionProduct,GoldenInt.eval_add,GoldenInt.eval_sub,
      GoldenInt.eval_mul,Matrix.mul_apply,quaternion,Q0,Q1,Q2,Q3,Holant.Signature.equality] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem quaternionCoefficient_smul (c : ℂ) (U : Binary) (i : Fin 4) :
    quaternionCoefficient (c • U) i = c * quaternionCoefficient U i := by
  fin_cases i <;> simp [quaternionCoefficient,smul_eq_mul] <;> ring

def goldenCross (u v : GoldenVector) (a b : Fin 4) : GoldenInt :=
  GoldenInt.sub (GoldenInt.mul (u a) (v b)) (GoldenInt.mul (u b) (v a))

theorem goldenCross_projective_zero (u v : GoldenVector) (c : ℂ)
    (h : goldenMatrix u = c • goldenMatrix v) (a b : Fin 4) :
    GoldenInt.eval (goldenCross u v a b) = 0 := by
  change quaternion (fun i => GoldenInt.eval (u i)) = (c • quaternion (fun i => GoldenInt.eval (v i)) : Binary) at h
  have ha := congrArg (fun U => quaternionCoefficient U a) h
  have hb := congrArg (fun U => quaternionCoefficient U b) h
  simp only [goldenMatrix,quaternionCoefficient_smul,quaternionCoefficient_quaternion] at ha hb
  apply Complex.ofReal_injective
  simp only [goldenCross,GoldenInt.eval_sub,GoldenInt.eval_mul,Complex.ofReal_sub,
    Complex.ofReal_mul,Complex.ofReal_zero]
  rw [ha,hb]
  ring

end Holant.Certificates.RainbowOrbit
