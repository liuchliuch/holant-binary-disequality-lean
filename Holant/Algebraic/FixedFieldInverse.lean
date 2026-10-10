import Holant.Algebraic.FixedField
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Exact inversion from the fixed rational structure table. This module proves
the arithmetic formula, including inverse zero. Its actual finite-stack compiler
is a separate obligation; matrix inversion is not charged as one machine step. -/
namespace Holant.Algebraic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace ArithmeticData
variable {n : ℕ}

/-- Column j records multiplication of the input by the jth basis vector. -/
def multiplicationMatrix (D : ArithmeticData n) (v : Fin n→ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun k j => ∑i,v i*D.mulTable i j k

theorem multiplicationMatrix_mulVec (D : ArithmeticData n) (v w : Fin n→ℚ) :
    (D.multiplicationMatrix v).mulVec w=D.mulCode v w := by
  ext k
  simp only [multiplicationMatrix,Matrix.mulVec,dotProduct,Finset.sum_mul,mulCode,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal rational determinant/adjugate formula, using only fixed-size data. -/
def inverseCode (D : ArithmeticData n) (v : Fin n→ℚ) : Fin n→ℚ :=
  ((D.multiplicationMatrix v).det⁻¹ • (D.multiplicationMatrix v).adjugate).mulVec D.unitCode

theorem inverseCode_apply (D : ArithmeticData n) (v : Fin n→ℚ) (k : Fin n) :
    D.inverseCode v k=(D.multiplicationMatrix v).det⁻¹*
      ((D.multiplicationMatrix v).updateCol k D.unitCode).det := by
  simp only [inverseCode,Matrix.smul_mulVec,←Matrix.cramer_eq_adjugate_mulVec,
    Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply]

theorem inverseCode_eq_inverse_matrix (D : ArithmeticData n) (v : Fin n→ℚ) :
    D.inverseCode v=((D.multiplicationMatrix v)⁻¹).mulVec D.unitCode := by
  rw [inverseCode,Matrix.inv_def,Ring.inverse_eq_inv]

@[simp] theorem multiplicationMatrix_zero (D : ArithmeticData n) :
    D.multiplicationMatrix 0=0 := by ext k j; simp [multiplicationMatrix]

@[simp] theorem inverseCode_zero (D : ArithmeticData n) : D.inverseCode 0=0 := by
  rw [inverseCode_eq_inverse_matrix,multiplicationMatrix_zero,Matrix.inv_zero]
  simp

end ArithmeticData

namespace FixedField
noncomputable section
variable {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}

theorem multiplicationMatrix_isUnit (F : FixedField K n) (v : Fin n→ℚ) (hv : v≠0) :
    IsUnit (F.toArithmeticData.multiplicationMatrix v) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u w he
  rw [ArithmeticData.multiplicationMatrix_mulVec,ArithmeticData.multiplicationMatrix_mulVec] at he
  change F.mulCode v u=F.mulCode v w at he
  apply F.decode_injective
  have hn : F.decode v≠0 := by
    intro hz
    apply hv
    apply F.decode_injective
    simpa using hz
  apply mul_left_cancel₀ hn
  rw [←F.decode_mul,←F.decode_mul]
  exact congrArg F.decode he

/-- The fixed-table formula really returns the inverse in the original field. -/
theorem decode_inverseCode (F : FixedField K n) (v : Fin n→ℚ) :
    F.decode (F.toArithmeticData.inverseCode v)=(F.decode v)⁻¹ := by
  by_cases hv : v=0
  · subst v
    simp
  · have hu := (F.toArithmeticData.multiplicationMatrix v).isUnit_iff_isUnit_det.mp
      (F.multiplicationMatrix_isUnit v hv)
    have he : F.mulCode v (F.toArithmeticData.inverseCode v)=F.unitCode := by
      change F.toArithmeticData.mulCode v _=F.unitCode
      rw [←ArithmeticData.multiplicationMatrix_mulVec,
        ArithmeticData.inverseCode_eq_inverse_matrix,Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
    have hp : F.decode v*F.decode (F.toArithmeticData.inverseCode v)=1 := by
      rw [←decode_mul,he,decode_unit]
    exact inv_eq_of_mul_eq_one_right hp |>.symm

end
end FixedField
end Holant.Algebraic
