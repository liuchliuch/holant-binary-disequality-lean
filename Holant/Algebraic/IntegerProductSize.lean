import Holant.Algebraic.IntegerScaling

/-! General fixed-dimensional coordinate bounds for sums of products, preserving
one common denominator through the entire sum. -/

namespace Holant.Algebraic.IntegerArithmeticData

open scoped BigOperators

variable {n L k : ℕ}

/-- Integer coordinates of a sum of `L` products, each having degree `k`. -/
def sumProductNumerator (I : IntegerArithmeticData n)
    (a : Fin L → Fin k → Fin n → ℤ) : Fin n → ℤ :=
  ∑ t, I.productNumerator (List.ofFn (a t))

/-- The actual rational-table computation for the same sum of products. -/
def sumProductCode (I : IntegerArithmeticData n) (D : ℕ)
    (a : Fin L → Fin k → Fin n → ℤ) : Fin n → ℚ :=
  ∑ t, (I.rationalData D).productCode ((List.ofFn (a t)).map (scaledCoordinates D))

/-- A single common denominator survives the entire exponentially large sum. -/
theorem sumProductCode_scaled (I : IntegerArithmeticData n) (D : ℕ)
    (a : Fin L → Fin k → Fin n → ℤ) :
    I.sumProductCode D a = scaledCoordinates (D ^ (2 * k + 1)) (I.sumProductNumerator a) := by
  simp only [sumProductCode, productCode_scaled, List.length_ofFn, productDenominator_eq,
    sumProductNumerator, sum_scaledCoordinates]

/-- Explicit integer-numerator magnitude bound. -/
theorem sumProductNumerator_natAbs_le (I : IntegerArithmeticData n) (M : ℕ)
    (hu : ∀ i, (I.unit i).natAbs ≤ M) (ht : ∀ i j z, (I.table i j z).natAbs ≤ M)
    (a : Fin L → Fin k → Fin n → ℤ) (ha : ∀ t i z, (a t i z).natAbs ≤ M) (z : Fin n) :
    (I.sumProductNumerator a z).natAbs ≤ L * M * (n * n * M * M) ^ k := by
  have hp (t : Fin L) : (I.productNumerator (List.ofFn (a t)) z).natAbs ≤
      M * (n * n * M * M) ^ k := by
    have hinput : ∀ v ∈ List.ofFn (a t), ∀ i, (v i).natAbs ≤ M := by
      intro v hv i
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hv
      exact ha t j i
    simpa using I.productNumerator_natAbs_le M hu ht (List.ofFn (a t)) hinput z
  simp only [sumProductNumerator, Finset.sum_apply]
  calc
    (∑ t, I.productNumerator (List.ofFn (a t)) z).natAbs ≤
      ∑ t, (I.productNumerator (List.ofFn (a t)) z).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _t : Fin L, M * (n * n * M * M) ^ k := Finset.sum_le_sum (fun t _ => hp t)
    _ = L * M * (n * n * M * M) ^ k := by simp [Nat.mul_assoc]

/-- Magnitude bound for each canonical rational coordinate after cancellation. -/
theorem sumProductCode_height_le (I : IntegerArithmeticData n) (D M : ℕ) (hD : 0 < D)
    (hu : ∀ i, (I.unit i).natAbs ≤ M) (ht : ∀ i j z, (I.table i j z).natAbs ≤ M)
    (a : Fin L → Fin k → Fin n → ℤ) (ha : ∀ t i z, (a t i z).natAbs ≤ M) (z : Fin n) :
    rationalHeight (I.sumProductCode D a z) ≤
      max (L * M * (n * n * M * M) ^ k) (D ^ (2 * k + 1)) := by
  rw [sumProductCode_scaled]
  have hd : ((D ^ (2 * k + 1) : ℕ) : ℤ) ≠ 0 := by positivity
  have hn := divInt_num_le (I.sumProductNumerator a z) ((D ^ (2 * k + 1) : ℕ) : ℤ) hd
  have hden := divInt_den_le (I.sumProductNumerator a z) ((D ^ (2 * k + 1) : ℕ) : ℤ) hd
  rw [Rat.divInt_eq_div] at hn hden
  simp only [Int.cast_natCast, Int.natAbs_natCast] at hn hden
  exact max_le_max (le_trans hn (I.sumProductNumerator_natAbs_le M hu ht a ha z)) hden

/-- A bound linear in product degree and logarithmic in summand count. All other
parameters are fixed when the field and coefficient family are fixed. -/
def coordinateBitBound (n L k D M : ℕ) : ℕ :=
  L.size + M.size + k * (n * n * M * M).size + (2 * k + 1) * D.size + 1

theorem sumProductCode_bitHeight_le (I : IntegerArithmeticData n) (D M : ℕ) (hD : 0 < D)
    (hu : ∀ i, (I.unit i).natAbs ≤ M) (ht : ∀ i j z, (I.table i j z).natAbs ≤ M)
    (a : Fin L → Fin k → Fin n → ℤ) (ha : ∀ t i z, (a t i z).natAbs ≤ M) (z : Fin n) :
    rationalBitHeight (I.sumProductCode D a z) ≤ coordinateBitBound n L k D M := by
  have hN := natSize_mul_le (L * M) ((n * n * M * M) ^ k)
  have hLM := natSize_mul_le L M
  have hPow := natSize_pow_le (n * n * M * M) k
  have hDen := natSize_pow_le D (2 * k + 1)
  apply le_trans (Nat.size_le_size (I.sumProductCode_height_le D M hD hu ht a ha z))
  apply Nat.size_le.mpr
  apply max_lt
  · apply Nat.size_le.mp
    unfold coordinateBitBound
    omega
  · apply Nat.size_le.mp
    unfold coordinateBitBound
    omega

/-- The bound applies to actual faithful vector bitstrings, including framing. -/
theorem sumProductCode_encoded_length_le (I : IntegerArithmeticData n) (D M : ℕ) (hD : 0 < D)
    (hu : ∀ i, (I.unit i).natAbs ≤ M) (ht : ∀ i j z, (I.table i j z).natAbs ≤ M)
    (a : Fin L → Fin k → Fin n → ℤ) (ha : ∀ t i z, (a t i z).natAbs ≤ M) :
    ((vectorEncoding n).encode (I.sumProductCode D a)).length ≤
      n * (4 * (coordinateBitBound n L k D M + 1) + 1) := by
  apply vectorEncoding_length_le
  intro z
  have hz := I.sumProductCode_bitHeight_le D M hD hu ht a ha z
  apply max_le
  · apply Nat.add_le_add_right
    exact le_trans (Nat.size_le_size (le_max_left _ _)) hz
  · exact le_trans (le_trans (Nat.size_le_size (le_max_right _ _)) hz) (Nat.le_succ _)

/-- In particular, an exponential number of summands contributes only its
exponent to the answer's bit length. -/
theorem sumProductCode_encoded_length_le_exponential (I : IntegerArithmeticData n)
    (D M e : ℕ) (hD : 0 < D) (hL : L ≤ 2 ^ e)
    (hu : ∀ i, (I.unit i).natAbs ≤ M) (ht : ∀ i j z, (I.table i j z).natAbs ≤ M)
    (a : Fin L → Fin k → Fin n → ℤ) (ha : ∀ t i z, (a t i z).natAbs ≤ M) :
    ((vectorEncoding n).encode (I.sumProductCode D a)).length ≤
      n * (4 * (e + M.size + k * (n * n * M * M).size + (2 * k + 1) * D.size + 3) + 1) := by
  apply le_trans (I.sumProductCode_encoded_length_le D M hD hu ht a ha)
  apply Nat.mul_le_mul_left
  have hsize := Nat.size_le_size hL
  rw [Nat.size_pow] at hsize
  unfold coordinateBitBound
  omega

end Holant.Algebraic.IntegerArithmeticData
