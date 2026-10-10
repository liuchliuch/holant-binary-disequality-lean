import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.BinaryArithmetic.Unpairing


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
open _root_.Holant.Complexity
open _root_.Holant.Complexity.BinaryArithmetic


/-! Genuine polynomial-time decoding of the literal square-shell Nat.pair code.
The input is ordinary encodeNat; the output is the existing faithful framed pair
codec, with all input and scratch stacks empty and finite registers reset. -/

namespace Holant.Complexity.BinaryArithmetic.EncodedUnpairing
open Turing Computability

abbrev outputEncoding := EncodedAddition.inputEncoding
abbrev computer := Unpairing.computer

/-- Literal codec compatibility from one canonical word to one canonical pair. -/
theorem encoded_exact (n : ℕ) :
    Unpairing.Runs (initList computer (encodeNat n))
      (haltList computer (outputEncoding.encode (Nat.unpair n)))
      (Unpairing.computeTime (encodeNat n)) := by
  have h := Unpairing.compute_exact (encodeNat n)
  rw [PairingBits.unpairBits_encodeNat] at h
  exact h

noncomputable def unpairPolyTime : PolyTime encodingNatBool outputEncoding Nat.unpair where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X ^ 2 + 22 * Polynomial.X + 9
  outputsFun n := by
    change TM2OutputsInTime computer (List.map id (encodeNat n))
      (some (List.map id (outputEncoding.encode (Nat.unpair n))))
      ((6 * Polynomial.X ^ 2 + 22 * Polynomial.X + 9).eval (encodeNat n).length)
    rw [List.map_id, List.map_id]
    refine { steps := Unpairing.computeTime (encodeNat n)
             evals_in_steps := encoded_exact n
             steps_le_m := ?_ }
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow] using Unpairing.computeTime_le (encodeNat n)
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem unpair_inFP : InFP encodingNatBool outputEncoding Nat.unpair := ⟨unpairPolyTime⟩

/-- Round trip for the exact pairing function used in RationalEncoding. -/
theorem encoded_pair_exact (a b : ℕ) :
    Unpairing.Runs (initList computer (encodeNat (Nat.pair a b)))
      (haltList computer (outputEncoding.encode (a,b)))
      (Unpairing.computeTime (encodeNat (Nat.pair a b))) := by
  simpa only [Nat.unpair_pair] using encoded_exact (Nat.pair a b)

/-- The unchanged rational numerator code and denominator are recovered exactly. -/
theorem encoded_rational_pair_exact (q : ℚ) :
    Unpairing.Runs
      (initList computer (encodeNat (Nat.pair (Equiv.intEquivNat q.num) q.den)))
      (haltList computer (outputEncoding.encode (Equiv.intEquivNat q.num, q.den)))
      (Unpairing.computeTime (encodeNat (Nat.pair (Equiv.intEquivNat q.num) q.den))) :=
  encoded_pair_exact _ _

end Holant.Complexity.BinaryArithmetic.EncodedUnpairing

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
