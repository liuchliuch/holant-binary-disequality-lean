import Holant.Algebraic.IntegerProductSize

/-!
# General fixed-number-field answer sizes

One computable common denominator clears the fixed rational unit coordinates,
multiplication table, and finite coefficient family. The proved integer invariant
then bounds a sum of exponentially many bounded-degree field products. The final
bound concerns the actual faithful binary encoding of the semantic field answer.
The constants depend on the fixed field presentation/family, as the paper requires.
-/

namespace Holant.Algebraic

open scoped BigOperators

namespace ArithmeticData

variable {n : ℕ} {A : Type*} [Fintype A]

/-- The entire fixed scalar table needed for a finite field-coefficient family. -/
abbrev ConstantIndex (A : Type*) (n : ℕ) :=
  Fin n ⊕ ((Fin n × Fin n × Fin n) ⊕ (A × Fin n))

/-- Include unit, structure constants, and input-family coordinates together. -/
def scalarTable (D : ArithmeticData n) (coeff : A → Fin n → ℚ) : ConstantIndex A n → ℚ
  | .inl i => D.unitCode i
  | .inr (.inl (i, j, k)) => D.mulTable i j k
  | .inr (.inr (a, i)) => coeff a i

def familyDenominator (D : ArithmeticData n) (coeff : A → Fin n → ℚ) : ℕ :=
  commonDenominator (D.scalarTable coeff)

def familyBound (D : ArithmeticData n) (coeff : A → Fin n → ℚ) : ℕ :=
  Holant.Algebraic.familyNumeratorBound (D.scalarTable coeff)

/-- Concrete integer structure constants with no chosen semantic values. -/
def clearedData (D : ArithmeticData n) (coeff : A → Fin n → ℚ) : IntegerArithmeticData n where
  unit i := clearedNumerator (D.scalarTable coeff) (.inl i)
  table i j k := clearedNumerator (D.scalarTable coeff) (.inr (.inl (i, j, k)))

def clearedCoefficient (D : ArithmeticData n) (coeff : A → Fin n → ℚ) (a : A) : Fin n → ℤ :=
  fun i => clearedNumerator (D.scalarTable coeff) (.inr (.inr (a, i)))

theorem familyDenominator_pos (D : ArithmeticData n) (coeff : A → Fin n → ℚ) :
    0 < D.familyDenominator coeff := commonDenominator_pos _

/-- Clearing and reinterpreting the table recovers the original arithmetic data. -/
theorem clearedData_rationalData (D : ArithmeticData n) (coeff : A → Fin n → ℚ) :
    (D.clearedData coeff).rationalData (D.familyDenominator coeff) = D := by
  apply ArithmeticData.ext
  · funext i
    exact clearedNumerator_correct (D.scalarTable coeff) (.inl i)
  · funext i j k
    exact clearedNumerator_correct (D.scalarTable coeff) (.inr (.inl (i, j, k)))

@[simp] theorem clearedCoefficient_scaled (D : ArithmeticData n) (coeff : A → Fin n → ℚ) (a : A) :
    scaledCoordinates (D.familyDenominator coeff) (D.clearedCoefficient coeff a) = coeff a := by
  funext i
  exact clearedNumerator_correct (D.scalarTable coeff) (.inr (.inr (a, i)))

theorem cleared_unit_le (D : ArithmeticData n) (coeff : A → Fin n → ℚ) (i : Fin n) :
    ((D.clearedData coeff).unit i).natAbs ≤ D.familyBound coeff :=
  clearedNumerator_le (D.scalarTable coeff) (.inl i)

theorem cleared_table_le (D : ArithmeticData n) (coeff : A → Fin n → ℚ) (i j k : Fin n) :
    ((D.clearedData coeff).table i j k).natAbs ≤ D.familyBound coeff :=
  clearedNumerator_le (D.scalarTable coeff) (.inr (.inl (i, j, k)))

theorem cleared_coefficient_le (D : ArithmeticData n) (coeff : A → Fin n → ℚ) (a : A) (i : Fin n) :
    (D.clearedCoefficient coeff a i).natAbs ≤ D.familyBound coeff :=
  clearedNumerator_le (D.scalarTable coeff) (.inr (.inr (a, i)))

/-- The actual finite sum of fixed-family products in rational coordinates. -/
def sumProducts (D : ArithmeticData n) (coeff : A → Fin n → ℚ) {L k : ℕ}
    (labels : Fin L → Fin k → A) : Fin n → ℚ :=
  ∑ t, D.productCode (List.ofFn (fun i => coeff (labels t i)))

/-- The cleared computation exactly represents the original coordinate computation. -/
theorem sumProducts_eq_cleared (D : ArithmeticData n) (coeff : A → Fin n → ℚ) {L k : ℕ}
    (labels : Fin L → Fin k → A) :
    D.sumProducts coeff labels =
      (D.clearedData coeff).sumProductCode (D.familyDenominator coeff)
        (fun t i => D.clearedCoefficient coeff (labels t i)) := by
  simp only [IntegerArithmeticData.sumProductCode, clearedData_rationalData,
    List.map_ofFn, Function.comp_def, clearedCoefficient_scaled, sumProducts]

/-- Exact bound before replacing summand count by an exponential estimate. -/
theorem sumProducts_encoded_length_le (D : ArithmeticData n) (coeff : A → Fin n → ℚ) {L k : ℕ}
    (labels : Fin L → Fin k → A) :
    ((vectorEncoding n).encode (D.sumProducts coeff labels)).length ≤
      n * (4 * (IntegerArithmeticData.coordinateBitBound n L k
        (D.familyDenominator coeff) (D.familyBound coeff) + 1) + 1) := by
  rw [D.sumProducts_eq_cleared coeff labels]
  exact (D.clearedData coeff).sumProductCode_encoded_length_le _ _
    (D.familyDenominator_pos coeff) (D.cleared_unit_le coeff) (D.cleared_table_le coeff) _
    (fun t i z => D.cleared_coefficient_le coeff (labels t i) z)

/-- General fixed-dimension answer length: linear in degree and in the logarithm
of the number of summands. -/
theorem sumProducts_encoded_length_le_exponential (D : ArithmeticData n)
    (coeff : A → Fin n → ℚ) {L k e : ℕ} (labels : Fin L → Fin k → A) (hL : L ≤ 2 ^ e) :
    ((vectorEncoding n).encode (D.sumProducts coeff labels)).length ≤
      n * (4 * (e + (D.familyBound coeff).size +
        k * (n * n * D.familyBound coeff * D.familyBound coeff).size +
        (2 * k + 1) * (D.familyDenominator coeff).size + 3) + 1) := by
  rw [D.sumProducts_eq_cleared coeff labels]
  exact (D.clearedData coeff).sumProductCode_encoded_length_le_exponential _ _ e
    (D.familyDenominator_pos coeff) hL (D.cleared_unit_le coeff) (D.cleared_table_le coeff) _
    (fun t i z => D.cleared_coefficient_le coeff (labels t i) z)

end ArithmeticData

namespace FixedField

variable {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}

/-- A faithful binary encoding of semantic field elements, specified through the
chosen rational basis. Computations can operate entirely on their coefficient
vectors, without evaluating abstract field elements. -/
noncomputable def encoding (F : FixedField K n) : Computability.Encoding K Bool where
  encode x := (vectorEncoding n).encode (F.basis.equivFun x)
  decode bits := ((vectorEncoding n).decode bits).map F.decode
  decode_encode x := by simp [decode]

@[simp] theorem encoding_decode (F : FixedField K n) (v : Fin n → ℚ) :
    F.encoding.encode (F.decode v) = (vectorEncoding n).encode v := by
  change (vectorEncoding n).encode (F.basis.equivFun (F.basis.equivFun.symm v)) = _
  rw [F.basis.equivFun.apply_symm_apply]

/-- The coordinate product computes the actual field product, including the
empty product's unit. -/
@[simp] theorem decode_productCode (F : FixedField K n) (vs : List (Fin n → ℚ)) :
    F.decode (F.toArithmeticData.productCode vs) = (vs.map F.decode).prod := by
  induction vs with
  | nil => exact F.unit_spec
  | cons v vs ih =>
    change F.decode (F.mulCode v (F.toArithmeticData.productCode vs)) =
      F.decode v * (vs.map F.decode).prod
    rw [F.decode_mul, ih]

/-- The coordinate answer is the semantic field-valued sum of products. -/
@[simp] theorem decode_sumProducts (F : FixedField K n) {A : Type*} [Fintype A]
    (coeff : A → Fin n → ℚ) {L k : ℕ} (labels : Fin L → Fin k → A) :
    F.decode (F.toArithmeticData.sumProducts coeff labels) =
      ∑ t, ∏ i, F.decode (coeff (labels t i)) := by
  simp [ArithmeticData.sumProducts, map_sum, List.map_ofFn, List.prod_ofFn]

/-- This is the field-answer bit bound, with faithful encoding and no coordinate
interpretation gap remaining. -/
theorem sumProducts_answer_length_le_exponential (F : FixedField K n)
    {A : Type*} [Fintype A] (coeff : A → Fin n → ℚ) {L k e : ℕ}
    (labels : Fin L → Fin k → A) (hL : L ≤ 2 ^ e) :
    (F.encoding.encode (∑ t, ∏ i, F.decode (coeff (labels t i)))).length ≤
      n * (4 * (e + (F.toArithmeticData.familyBound coeff).size +
        k * (n * n * F.toArithmeticData.familyBound coeff * F.toArithmeticData.familyBound coeff).size +
        (2 * k + 1) * (F.toArithmeticData.familyDenominator coeff).size + 3) + 1) := by
  rw [← F.decode_sumProducts coeff labels, F.encoding_decode]
  exact F.toArithmeticData.sumProducts_encoded_length_le_exponential coeff labels hL

end FixedField
end Holant.Algebraic
