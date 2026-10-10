import Holant.Algebraic.RationalEncoding
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Pi

/-!
# Effective addition and multiplication in a fixed number field

A presentation contains a finite rational basis, explicit rational coordinates for
one, and an explicit multiplication table. Arithmetic on coefficient vectors is
ordinary exact rational arithmetic and finite sums. Its interpretation is injective
and preserves addition and multiplication. Constructing such a presentation from
arbitrary algebraic input, inverse computation, coefficient growth, and bit-time
bounds are not proved here.
-/

namespace Holant.Algebraic

open Module
open scoped BigOperators

/-- Computational data contains no semantic field elements or chosen basis. -/
structure ArithmeticData (n : ℕ) where
  unitCode : Fin n → ℚ
  mulTable : Fin n → Fin n → (Fin n → ℚ)

namespace ArithmeticData

/-- Explicit fixed-table multiplication of rational vectors. -/
def mulCode {n : ℕ} (D : ArithmeticData n) (v w : Fin n → ℚ) : Fin n → ℚ :=
  ∑ i, ∑ j, (v i * w j) • D.mulTable i j

/-- Arithmetic expressions contain only exact coefficient constants and the two
ring operations required by partition-function evaluation. -/
inductive Expr (n : ℕ) where
  | constant : (Fin n → ℚ) → Expr n
  | add : Expr n → Expr n → Expr n
  | mul : Expr n → Expr n → Expr n

/-- This evaluator accepts only rational data, so no noncomputable semantic
basis is needed to run it. -/
def evalCode {n : ℕ} (D : ArithmeticData n) : Expr n → (Fin n → ℚ)
  | .constant v => v
  | .add a b => D.evalCode a + D.evalCode b
  | .mul a b => D.mulCode (D.evalCode a) (D.evalCode b)

/-- The executable evaluator's binary output. -/
def evalBits {n : ℕ} (D : ArithmeticData n) (e : Expr n) : List Bool :=
  (vectorEncoding n).encode (D.evalCode e)

@[simp] theorem decode_evalBits {n : ℕ} (D : ArithmeticData n) (e : Expr n) :
    (vectorEncoding n).decode (D.evalBits e) = some (D.evalCode e) :=
  (vectorEncoding n).decode_encode _

end ArithmeticData

/-- The semantic field is only used to state and prove correctness. The table and
unit coordinates are finite rational data, supplied as part of the presentation. -/
structure FixedField (K : Type*) [Field K] [Algebra ℚ K] (n : ℕ)
    extends ArithmeticData n where
  basis : Basis (Fin n) ℚ K
  unit_spec : basis.equivFun.symm unitCode = 1
  mul_spec : ∀ i j, basis.equivFun.symm (mulTable i j) = basis i * basis j

namespace FixedField

variable {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}

/-- Interpretation of a rational coefficient vector in the fixed basis. -/
noncomputable def decode (F : FixedField K n) : (Fin n → ℚ) ≃ₗ[ℚ] K :=
  F.basis.equivFun.symm

theorem decode_injective (F : FixedField K n) : Function.Injective F.decode :=
  F.decode.injective

@[simp] theorem decode_unit (F : FixedField K n) : F.decode F.unitCode = 1 := F.unit_spec

@[simp] theorem decode_table (F : FixedField K n) (i j : Fin n) :
    F.decode (F.mulTable i j) = F.basis i * F.basis j := F.mul_spec i j

/-- Executable coordinatewise addition. -/
def addCode (v w : Fin n → ℚ) : Fin n → ℚ := v + w

/-- Executable multiplication using the fixed rational structure constants. -/
def mulCode (F : FixedField K n) (v w : Fin n → ℚ) : Fin n → ℚ :=
  F.toArithmeticData.mulCode v w

@[simp] theorem mulCode_apply (F : FixedField K n) (v w : Fin n → ℚ) (k : Fin n) :
    F.mulCode v w k = ∑ i, ∑ j, (v i * w j) * F.mulTable i j k := by
  simp [mulCode, ArithmeticData.mulCode, Finset.sum_apply]

@[simp] theorem decode_add (F : FixedField K n) (v w : Fin n → ℚ) :
    F.decode (addCode v w) = F.decode v + F.decode w := F.decode.map_add v w

/-- Exact multiplication correctness, with no numerical approximation. -/
@[simp] theorem decode_mul (F : FixedField K n) (v w : Fin n → ℚ) :
    F.decode (F.mulCode v w) = F.decode v * F.decode w := by
  simp only [mulCode, ArithmeticData.mulCode, map_sum, map_smul, decode_table]
  conv_rhs => rw [show F.decode v = ∑ i, v i • F.basis i from F.basis.equivFun_symm_apply v]
  conv_rhs => rw [show F.decode w = ∑ j, w j • F.basis j from F.basis.equivFun_symm_apply w]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  exact Finset.sum_comm

/-- Equality of coefficient vectors is exactly equality of represented values. -/
theorem decode_eq_iff (F : FixedField K n) (v w : Fin n → ℚ) :
    F.decode v = F.decode w ↔ v = w := F.decode.injective.eq_iff

/-- Associativity is derived from field semantics and injectivity, not postulated. -/
theorem mulCode_assoc (F : FixedField K n) (u v w : Fin n → ℚ) :
    F.mulCode (F.mulCode u v) w = F.mulCode u (F.mulCode v w) := by
  apply F.decode_injective
  simp [mul_assoc]

theorem mulCode_comm (F : FixedField K n) (v w : Fin n → ℚ) :
    F.mulCode v w = F.mulCode w v := by
  apply F.decode_injective
  simp [mul_comm]

@[simp] theorem mulCode_unit (F : FixedField K n) (v : Fin n → ℚ) :
    F.mulCode v F.unitCode = v := by
  apply F.decode_injective
  simp

abbrev Expr := ArithmeticData.Expr

/-- Convenience specialization of the computational-data-only evaluator. -/
abbrev evalCode (F : FixedField K n) := F.toArithmeticData.evalCode

/-- Independent evaluation in the semantic field. -/
noncomputable def eval (F : FixedField K n) : Expr n → K
  | .constant v => F.decode v
  | .add a b => F.eval a + F.eval b
  | .mul a b => F.eval a * F.eval b

/-- Every exact arithmetic expression is correctly evaluated by coefficient code. -/
@[simp] theorem decode_evalCode (F : FixedField K n) (e : Expr n) :
    F.decode (F.evalCode e) = F.eval e := by
  induction e with
  | constant v => rfl
  | add a b ha hb =>
    change F.decode (addCode (F.evalCode a) (F.evalCode b)) = F.eval a + F.eval b
    rw [decode_add, ha, hb]
  | mul a b ha hb =>
    change F.decode (F.mulCode (F.evalCode a) (F.evalCode b)) = F.eval a * F.eval b
    rw [decode_mul, ha, hb]

/-- The final answer has a faithful binary coefficient encoding. -/
def evalBits (F : FixedField K n) (e : Expr n) : List Bool :=
  (vectorEncoding n).encode (F.evalCode e)

@[simp] theorem decode_evalBits (F : FixedField K n) (e : Expr n) :
    (vectorEncoding n).decode (F.evalBits e) = some (F.evalCode e) :=
  (vectorEncoding n).decode_encode _

end FixedField
end Holant.Algebraic
