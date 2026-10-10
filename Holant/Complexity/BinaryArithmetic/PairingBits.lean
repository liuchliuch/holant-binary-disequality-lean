import Holant.Complexity.BinaryArithmetic.SquareRootBits
import Holant.Complexity.BinaryArithmetic.MultiplyBits
import Mathlib.Data.Nat.Pairing
import Holant.Algebraic.EncodingSize

/-!
# Binary algorithms for the literal rational-code pairing

The fixed-field scalar codec uses mathlib's square-shell `Nat.pair`, not Cantor
triangular pairing. These algorithms use genuine bitwise arithmetic, including
restoring square root for the inverse. The equations below establish exact codec
compatibility; finite-machine compilation and bit-time bounds are still separate.
-/

namespace Holant.Complexity.BinaryArithmetic.PairingBits

open Computability

/-- Literal square-shell pairing using the final subtraction borrow for a<b. -/
def pairBits (a b : List Bool) : List Bool :=
  if (subBits false a b).2 then
    addBits false (MultiplyBits.run b b.reverse []) a
  else
    addBits false (addBits false (MultiplyBits.run a a.reverse []) a) b

/-- Invert the exact codec by a restoring root and its already computed square
remainder. No host square root or unpair operation appears in the algorithm. -/
def unpairBits (word : List Bool) : List Bool × List Bool :=
  let qr := SquareRootBits.sqrtBits word
  let d := subBits false qr.2 qr.1
  if d.2 then (qr.2, qr.1) else (qr.1, normalize d.1)

private theorem borrow_encodeNat (a b : ℕ) :
    (subBits false (encodeNat a) (encodeNat b)).2 = decide (a < b) := by
  have h := subBits_borrow_iff false (encodeNat a) (encodeNat b)
  simp only [value_encodeNat, Bool.toNat_false, Nat.add_zero] at h
  cases hb : (subBits false (encodeNat a) (encodeNat b)).2 <;> simp_all

/-- Exact forward compatibility with the unchanged rational encoding convention. -/
theorem pairBits_encodeNat (a b : ℕ) :
    pairBits (encodeNat a) (encodeNat b) = encodeNat (Nat.pair a b) := by
  simp only [pairBits, borrow_encodeNat, decide_eq_true_eq, MultiplyBits.run_encodeNat,
    addBits_encodeNat, Nat.pair]
  split <;> rfl

/-- Exact inverse compatibility, including both shell branches and zero. -/
theorem unpairBits_encodeNat (n : ℕ) :
    unpairBits (encodeNat n) =
      (encodeNat (Nat.unpair n).1, encodeNat (Nat.unpair n).2) := by
  unfold unpairBits
  rw [SquareRootBits.sqrtBits_encodeNat]
  simp only [borrow_encodeNat, decide_eq_true_eq, Nat.unpair, Nat.pow_two]
  split
  · rfl
  · rename_i hn
    have hsub := subNatBits_encodeNat (n - Nat.sqrt n * Nat.sqrt n) (Nat.sqrt n)
    simp only [subNatBits, borrow_encodeNat, decide_eq_true_eq, hn, ↓reduceIte] at hsub
    exact congrArg (fun w => (encodeNat (Nat.sqrt n), w)) hsub

/-- Both decoded components are literal canonical words. -/
theorem unpairBits_pairBits (a b : ℕ) :
    unpairBits (pairBits (encodeNat a) (encodeNat b)) = (encodeNat a, encodeNat b) := by
  rw [pairBits_encodeNat, unpairBits_encodeNat, Nat.unpair_pair]

/-- Each decoded component fits in the original word length. -/
theorem unpairBits_lengths (n : ℕ) :
    (unpairBits (encodeNat n)).1.length ≤ (encodeNat n).length ∧
      (unpairBits (encodeNat n)).2.length ≤ (encodeNat n).length := by
  rw [unpairBits_encodeNat]
  constructor
  · apply DivisionBits.canonical_length_le_of_value_le _ _ (canonical_encodeNat _)
    simpa only [value_encodeNat] using Nat.unpair_left_le n
  · apply DivisionBits.canonical_length_le_of_value_le _ _ (canonical_encodeNat _)
    simpa only [value_encodeNat] using Nat.unpair_right_le n

/-- The literal packed code has at most twice the larger original bit length. -/
theorem pairBits_length (a b : ℕ) :
    (pairBits (encodeNat a) (encodeNat b)).length ≤
      2 * max (encodeNat a).length (encodeNat b).length := by
  rw [pairBits_encodeNat]
  simpa only [Algebraic.encodeNat_length] using Algebraic.pair_size_le a b

end Holant.Complexity.BinaryArithmetic.PairingBits
