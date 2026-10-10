import Holant.Algebraic.FixedField
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Concrete quadratic number fields

`quadraticData a b` is executable rational arithmetic for the relation
`ω² = a + bω`. When this polynomial has no rational root, mathlib supplies an
actual field with these coordinates. The basis/table presentation below connects
our finite arithmetic to that field. Gaussian rationals give a concrete
non-rational example with verified exact inverse computations.
-/

namespace Holant.Algebraic

open Module

/-- The complete two-dimensional multiplication table, in basis `(1, ω)`. -/
def quadraticData (a b : ℚ) : ArithmeticData 2 where
  unitCode := ![1, 0]
  mulTable := ![![![1, 0], ![0, 1]], ![![0, 1], ![a, b]]]

/-- A quadratic field presentation supplied by exact rational parameters and a
proof that its quadratic equation has no rational solution. -/
noncomputable def quadraticField (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)] :
    FixedField (QuadraticAlgebra ℚ a b) 2 where
  toArithmeticData := quadraticData a b
  basis := QuadraticAlgebra.basis a b
  unit_spec := by
    simp [quadraticData, QuadraticAlgebra.basis, Basis.equivFun_ofEquivFun]
    rfl
  mul_spec i j := by
    fin_cases i <;> fin_cases j <;>
      simp [quadraticData, QuadraticAlgebra.basis, Basis.equivFun_ofEquivFun]

/-- Coordinates are exactly the two stored rational components. -/
@[simp] theorem quadraticField_decode (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]
    (v : Fin 2 → ℚ) : (quadraticField a b).decode v = ⟨v 0, v 1⟩ := by
  simp [FixedField.decode, quadraticField, QuadraticAlgebra.basis, Basis.equivFun_ofEquivFun]

/-- Faithful bit encoding of the actual quadratic field, not just a symbolic tag. -/
def quadraticEncoding (a b : ℚ) : Computability.Encoding (QuadraticAlgebra ℚ a b) Bool where
  encode z := (vectorEncoding 2).encode ![z.re, z.im]
  decode bits := ((vectorEncoding 2).decode bits).map (fun v => ⟨v 0, v 1⟩)
  decode_encode z := by simp

/-- Exact coefficient inverse using the norm, with the conventional inverse of
zero equal to zero. Division here is only division of exact rationals. -/
def quadraticInverse (a b : ℚ) (v : Fin 2 → ℚ) : Fin 2 → ℚ :=
  let norm := v 0 * v 0 + b * v 0 * v 1 - a * v 1 * v 1
  ![(v 0 + b * v 1) / norm, -(v 1) / norm]

/-- The coefficient inverse agrees with the field inverse. -/
theorem quadraticInverse_correct (a b : ℚ) [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]
    (v : Fin 2 → ℚ) :
    (quadraticField a b).decode (quadraticInverse a b v) =
      ((quadraticField a b).decode v)⁻¹ := by
  simp only [quadraticField_decode]
  ext <;> simp [quadraticInverse, QuadraticAlgebra.inv_def, QuadraticAlgebra.norm_def,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- No rational square is negative one, so Gaussian rational arithmetic really
forms a field. This is a proved instance, not an assumption. -/
instance gaussian_no_root : Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) := by
  constructor
  intro r h
  have hr := sq_nonneg r
  norm_num at h
  linarith

abbrev GaussianRational := QuadraticAlgebra ℚ (-1) 0

def gaussianData : ArithmeticData 2 := quadraticData (-1) 0

noncomputable def gaussianField : FixedField GaussianRational 2 := quadraticField (-1) 0

def gaussianEncoding : Computability.Encoding GaussianRational Bool := quadraticEncoding (-1) 0

end Holant.Algebraic
