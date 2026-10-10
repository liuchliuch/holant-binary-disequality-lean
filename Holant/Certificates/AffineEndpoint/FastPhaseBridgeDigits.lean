import Holant.Certificates.AffineEndpoint.DigitPhaseRuntime

/-! The natural digit evaluator is related to the original phase code by
symbolic digit identities. No phase-code enumeration is used. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open DigitPhaseRuntime
set_option backward.isDefEq.respectTransparency false

theorem selectedDigits_eq_sum (base code mask n : Nat) :
    selectedDigits base code mask n =
      ∑ j : Fin n, if mask.testBit j.val then code / base^j.val % base else 0 := by
  induction n generalizing code mask with
  | zero => simp [selectedDigits]
  | succ n ih =>
    rw [selectedDigits, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.testBit_zero, decide_eq_true_eq, pow_zero, Nat.div_one,
      Fin.val_succ, Nat.testBit_succ, pow_succ', Nat.div_div_eq_div_mul]

theorem phaseDecode_linear_digit {d : Nat} (c : Fin (phaseCodeCount d)) (j : Fin d) :
    ((phaseDecode d c).1 j).val =
      c.val / 2^(mixedPairList d).length / 4^j.val % 4 := rfl

theorem phaseDecode_mixed_bit {d : Nat} (c : Fin (phaseCodeCount d)) (jk : MixedPair d) :
    (phaseDecode d c).2 jk = c.val.testBit (mixedPairPosition jk).val := by
  change decide ((⟨c.val % 2^(mixedPairList d).length /
    2^(mixedPairPosition jk).val % 2, _⟩ : Fin 2) = 1) = _
  simp only [Fin.ext_iff, Fin.val_one]
  rw [← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_mod_two_pow]
  simp [(mixedPairPosition jk).is_lt]

theorem two_mul_binary_digit (c i : Nat) :
    (if c.testBit i then (2 : ZMod 4) else 0) = 2 * (c / 2^i % 2 : Nat) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (c / 2^i) (by decide : 0 < 2)
  interval_cases c / 2^i % 2 <;> simp

theorem selectedDigits_cast (base code mask n : Nat) :
    (selectedDigits base code mask n : ZMod 4) =
      ∑ j : Fin n, (code / base^j.val % base : Nat) *
        bitValue (ZMod 4) (mask.testBit j.val) := by
  rw [selectedDigits_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  cases mask.testBit j.val <;> simp [bitValue]

end Holant.Certificates.AffineEndpoint
