import Holant.Algebraic.FixedField
import Holant.Algebraic.CommonDenominator
import Mathlib.Tactic.Ring

/-!
# Cleared integer coordinates for fixed-field products

All unit coordinates, multiplication-table entries, and input coefficients share
one positive denominator. Products preserve a degree-indexed common denominator;
integer-coordinate bounds grow exponentially only in product degree. Their binary
sizes therefore grow linearly in that degree. No arithmetic-machine runtime is
claimed here.
-/

namespace Holant.Algebraic

open scoped BigOperators

/-- A rational vector with one common natural denominator. -/
def scaledCoordinates {n : ℕ} (D : ℕ) (v : Fin n → ℤ) : Fin n → ℚ :=
  fun i => (v i : ℚ) / D

/-- Integer data obtained by clearing the rational unit and multiplication table. -/
structure IntegerArithmeticData (n : ℕ) where
  unit : Fin n → ℤ
  table : Fin n → Fin n → Fin n → ℤ

namespace ArithmeticData

@[ext] theorem ext {n : ℕ} {D E : ArithmeticData n}
    (hu : D.unitCode = E.unitCode) (ht : D.mulTable = E.mulTable) : D = E := by
  cases D
  cases E
  cases hu
  cases ht
  rfl

/-- Evaluate an ordered list of coefficient vectors with the actual table. -/
def productCode {n : ℕ} (D : ArithmeticData n) : List (Fin n → ℚ) → (Fin n → ℚ)
  | [] => D.unitCode
  | v :: vs => D.mulCode v (D.productCode vs)

end ArithmeticData

namespace IntegerArithmeticData

variable {n : ℕ}

/-- Interpret every stored integer using the same denominator. -/
def rationalData (I : IntegerArithmeticData n) (D : ℕ) : ArithmeticData n where
  unitCode := scaledCoordinates D I.unit
  mulTable i j := scaledCoordinates D (I.table i j)

/-- Exact numerator multiplication before rational normalization. -/
def mul (I : IntegerArithmeticData n) (v w : Fin n → ℤ) : Fin n → ℤ :=
  fun k => ∑ i, ∑ j, v i * w j * I.table i j k

/-- Clearing denominators commutes with the actual rational-vector multiplication. -/
theorem mul_scaled (I : IntegerArithmeticData n) (D A B : ℕ) (v w : Fin n → ℤ) :
    (I.rationalData D).mulCode (scaledCoordinates A v) (scaledCoordinates B w) =
      scaledCoordinates (A * B * D) (I.mul v w) := by
  funext k
  simp only [ArithmeticData.mulCode, rationalData, scaledCoordinates, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, mul, Int.cast_sum, Int.cast_mul, Nat.cast_mul,
    div_mul_div_comm, Finset.sum_div]

/-- The common denominator after `k` multiplications, including the initial unit. -/
def productDenominator (D : ℕ) : ℕ → ℕ
  | 0 => D
  | k + 1 => D * productDenominator D k * D

theorem productDenominator_eq (D k : ℕ) : productDenominator D k = D ^ (2 * k + 1) := by
  induction k with
  | zero => simp [productDenominator]
  | succ k ih =>
    rw [productDenominator, ih]
    have he : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [he]
    conv_rhs => rw [pow_add, pow_two]
    ring

/-- Exact integer product numerator, using the same recursion as rational arithmetic. -/
def productNumerator (I : IntegerArithmeticData n) : List (Fin n → ℤ) → (Fin n → ℤ)
  | [] => I.unit
  | v :: vs => I.mul v (I.productNumerator vs)

/-- All rational product coordinates share a denominator depending only on degree,
not on which fixed coefficient labels occurred. -/
theorem productCode_scaled (I : IntegerArithmeticData n) (D : ℕ) (vs : List (Fin n → ℤ)) :
    (I.rationalData D).productCode (vs.map (scaledCoordinates D)) =
      scaledCoordinates (productDenominator D vs.length) (I.productNumerator vs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons, ArithmeticData.productCode, productNumerator, List.length_cons,
      productDenominator, ih, mul_scaled]

/-- Coordinatewise integer multiplication bound with explicit dimension dependence. -/
theorem mul_natAbs_le (I : IntegerArithmeticData n) (v w : Fin n → ℤ) (A B C : ℕ)
    (hv : ∀ i, (v i).natAbs ≤ A) (hw : ∀ i, (w i).natAbs ≤ B)
    (ht : ∀ i j k, (I.table i j k).natAbs ≤ C) (k : Fin n) :
    (I.mul v w k).natAbs ≤ n * n * A * B * C := by
  unfold mul
  calc
    (∑ i, ∑ j, v i * w j * I.table i j k).natAbs ≤
        ∑ i, (∑ j, v i * w j * I.table i j k).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ i, ∑ j, (v i * w j * I.table i j k).natAbs := by
      exact Finset.sum_le_sum (fun i _ => Int.natAbs_sum_le _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, A * B * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [Int.natAbs_mul]
      exact Nat.mul_le_mul (Nat.mul_le_mul (hv i) (hw j)) (ht i j k)
    _ = n * n * A * B * C := by simp; ring

/-- Uniform fixed-table numerator bound along an arbitrary product. -/
theorem productNumerator_natAbs_le (I : IntegerArithmeticData n) (M : ℕ)
    (hu : ∀ i, (I.unit i).natAbs ≤ M) (ht : ∀ i j k, (I.table i j k).natAbs ≤ M)
    (vs : List (Fin n → ℤ)) (hv : ∀ v ∈ vs, ∀ i, (v i).natAbs ≤ M) (k : Fin n) :
    (I.productNumerator vs k).natAbs ≤ M * (n * n * M * M) ^ vs.length := by
  induction vs generalizing k with
  | nil => simpa [productNumerator] using hu k
  | cons v vs ih =>
    have hv' : ∀ i, (v i).natAbs ≤ M := hv v (by simp)
    have hvs : ∀ w ∈ vs, ∀ i, (w i).natAbs ≤ M := by
      intro w hw i
      exact hv w (by simp [hw]) i
    have hb : ∀ j, (I.productNumerator vs j).natAbs ≤ M * (n * n * M * M) ^ vs.length := by
      intro j
      exact ih hvs j
    have hm := I.mul_natAbs_le v (I.productNumerator vs) M
      (M * (n * n * M * M) ^ vs.length) M hv' hb ht k
    change (I.mul v (I.productNumerator vs) k).natAbs ≤ M * (n * n * M * M) ^ (vs.length + 1)
    calc
      _ ≤ n * n * M * (M * (n * n * M * M) ^ vs.length) * M := hm
      _ = M * (n * n * M * M) ^ (vs.length + 1) := by rw [pow_succ]; ring

end IntegerArithmeticData

/-- Adding common-denominator vectors adds only their integer numerators. -/
theorem sum_scaledCoordinates {n : ℕ} {ι : Type*} [Fintype ι]
    (D : ℕ) (v : ι → Fin n → ℤ) :
    (∑ i, scaledCoordinates D (v i)) = scaledCoordinates D (∑ i, v i) := by
  funext k
  simp [scaledCoordinates, Finset.sum_apply, Int.cast_sum, Finset.sum_div]

end Holant.Algebraic
