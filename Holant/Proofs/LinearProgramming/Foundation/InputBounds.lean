import Holant.Proofs.LinearProgramming.Foundation.DeterminantGap
import Holant.Complexity.BinaryArithmetic.SubtractBits

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Determinant bounds grounded in the actual raw A,b byte stream. Active-row
selectors below merely describe possible submatrices; no existence of an
active basis is assumed or asserted, and no selector is an LP input. BasicPoint supplies geometric existence separately from these input bit bounds.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.InputBounds
open Holant.Complexity Computability FixedFieldMachines GraphPreprocessing Codec

def size (d : Raw) : ℕ := (encoding.encode d).length

theorem length_formula (d : Raw) : size d = 2*d.rowCount + 2*d.dimension +
    2*(rowsEncoding.encode d.rows).length + (rowEncoding.encode d.rhs).length + 3 := by
  simp [size, encoding, wireEncoding, Raw.wire, pairEncoding, UnaryBinary.unaryEncoding,
    Holant.Algebraic.frame_length]
  omega

theorem dimension_le (d : Raw) : d.dimension ≤ size d := by rw [length_formula]; omega
theorem rows_length_le (d : Raw) : (rowsEncoding.encode d.rows).length ≤ size d := by
  rw [length_formula]; omega

private theorem member_length {α : Type} (e : Encoding α Bool) (xs : List α)
    (x : α) (hx : x ∈ xs) : (e.encode x).length ≤ ((framedListEncoding e).encode xs).length := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with rfl | ht
    · simp only [framedListEncoding, framedListEncode, List.length_cons, List.length_append,
        Holant.Algebraic.frame_length]
      omega
    · have h := ih ht
      simp only [framedListEncoding, framedListEncode, List.length_cons, List.length_append,
        Holant.Algebraic.frame_length] at h ⊢
      omega

theorem coefficient_length (d : Raw) (i : Fin d.rowCount) (j : Fin d.dimension) :
    (IntegerArithmetic.encoding.encode (d.coefficient i j)).length ≤ size d := by
  unfold Raw.coefficient
  by_cases hi : i.val < d.rows.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases hj : j.val < d.rows[i.val].length
    · rw [List.getD_eq_getElem _ _ hj]
      exact (member_length IntegerArithmetic.encoding _ _ (List.getElem_mem hj)).trans
        ((member_length rowEncoding _ _ (List.getElem_mem hi)).trans (rows_length_le d))
    · rw [List.getD_eq_default _ _ (by omega : d.rows[i.val].length ≤ j.val)]
      change 0 ≤ size d
      omega
  · rw [List.getD_eq_default _ _ (by omega : d.rows.length ≤ i.val)]
    change 0 ≤ size d
    exact Nat.zero_le _

theorem integer_magnitude (z : ℤ) : z.natAbs ≤ 2 ^ (IntegerArithmetic.encoding.encode z).length := by
  have hc : z.natAbs ≤ Equiv.intEquivNat z + 1 := by
    cases z with
    | ofNat n =>
      change n ≤ 2 * n + 1
      omega
    | negSucc n =>
      change n + 1 ≤ (2 * n + 1) + 1
      omega
  have hw := BinaryArithmetic.value_lt_pow_length (IntegerArithmetic.encoding.encode z)
  have hv : BinaryArithmetic.value (IntegerArithmetic.encoding.encode z) = Equiv.intEquivNat z := by
    simp [IntegerArithmetic.encoding]
  rw [hv] at hw
  omega

theorem coefficient_bound (d : Raw) (i : Fin d.rowCount) (j : Fin d.dimension) :
    |d.coefficient i j| ≤ (2 ^ size d : ℕ) := by
  have hn := (integer_magnitude (d.coefficient i j)).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (coefficient_length d i j))
  rw [← Int.natCast_natAbs]
  exact_mod_cast hn

abbrev Row (d : Raw) := Fin d.rowCount ⊕ Fin d.dimension
def row (d : Raw) (r : Row d) : Fin d.dimension → ℤ :=
  match r with
  | .inl i => d.coefficient i
  | .inr j => fun k => if j=k then 1 else 0

theorem row_bound (d : Raw) (r : Row d) (j : Fin d.dimension) :
    |row d r j| ≤ (2 ^ size d : ℕ) := by
  cases r with
  | inl i => exact coefficient_bound d i j
  | inr k =>
    have hp : (1 : ℕ) ≤ 2 ^ size d := Nat.one_le_pow _ _ (by decide)
    have hpz : (1 : ℤ) ≤ (2 ^ size d : ℕ) := by exact_mod_cast hp
    change |if k=j then (1 : ℤ) else 0| ≤ ((2 ^ size d : ℕ) : ℤ)
    split_ifs
    · simpa only [abs_one] using hpz
    · simpa only [abs_zero] using (le_trans (by norm_num : (0 : ℤ) ≤ 1) hpz)

def matrix (d : Raw) (select : Fin d.dimension → Row d) :
    Matrix (Fin d.dimension) (Fin d.dimension) ℤ := fun i => row d (select i)

/-- The same denominator bound for every possible active subsystem. -/
def denominator (d : Raw) : ℕ := 2 ^ (2 * size d ^ 2)

theorem denominator_pos (d : Raw) : 0 < denominator d := by unfold denominator; positivity

theorem determinant_bound (d : Raw) (select : Fin d.dimension → Row d) :
    |((matrix d select).det : ℚ)| ≤ (denominator d : ℚ) := by
  have hd := DeterminantGap.determinant_bound (matrix d select) (2 ^ size d)
    (fun i j => row_bound d (select i) j)
  have hp := DeterminantGap.bound_le_power d.dimension (2 ^ size d) (size d) le_rfl
  have hn := dimension_le d
  have he : d.dimension*d.dimension + size d*d.dimension ≤ 2*size d^2 := by
    have hs := Nat.mul_le_mul hn hn
    have ht := Nat.mul_le_mul_left (size d) hn
    nlinarith
  have hbound := hp.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) he)
  exact hd.trans (by exact_mod_cast hbound)

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.InputBounds
