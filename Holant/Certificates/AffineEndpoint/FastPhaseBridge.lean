import Holant.Certificates.AffineEndpoint.FastPhaseBridgeDigits

/-! Semantic correctness of the bounded natural arithmetic phase evaluator.
Only the dimension and the coordinate mask are split into finite cases; phase
codes remain symbolic throughout. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open DigitPhaseRuntime
set_option backward.isDefEq.respectTransparency false

theorem mixedPairList_length_small (d : Nat) (hd : d ≤ 4) :
    (mixedPairList d).length = d*(d-1)/2 := by
  interval_cases d <;> decide +kernel

theorem phaseQuadratic_decode_eval_digits (d : Nat) (c : Fin (phaseCodeCount d))
    (y : Fin d → Bool) :
    (phaseQuadratic (phaseDecode d c)).eval y =
      (∑ j : Fin d, (c.val / 2^(mixedPairList d).length / 4^j.val % 4 : Nat) *
        bitValue (ZMod 4) (y j)) +
      ∑ j : Fin d, ∑ k : Fin d, if h : j < k then
        (2 * (c.val / 2^(mixedPairPosition ⟨(j,k),h⟩).val % 2 : Nat) : ZMod 4) *
          bitValue (ZMod 4) (y j) * bitValue (ZMod 4) (y k) else 0 := by
  simp only [QuadraticPhase.eval, phaseQuadratic, zero_add,
    phaseDecode_linear_digit]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : j < k
  · simp [h, phaseDecode_mixed_bit, two_mul_binary_digit]
  · simp [h]

theorem mixedPairPosition_small (d : Nat) (hd : d ≤ 4) (p : MixedPair d) :
    (mixedPairPosition p).val = p.val.1.val * (2*d-p.val.1.val-1)/2 +
      (p.val.2.val-p.val.1.val-1) := by
  have h : ∀ d : Fin 5, ∀ p : MixedPair d.val,
      (mixedPairPosition p).val = p.val.1.val * (2*d.val-p.val.1.val-1)/2 +
        (p.val.2.val-p.val.1.val-1) := by decide +kernel
  exact h ⟨d, by omega⟩ p

theorem mixedMask_sum (d : Nat) (hd : d ≤ 4) (y : Fin 16) (f : Nat → ZMod 4) :
    (∑ j : Fin d, ∑ k : Fin d, if h : j < k then
      f (mixedPairPosition ⟨(j,k),h⟩).val * bitValue (ZMod 4) (y.val.testBit j.val) *
        bitValue (ZMod 4) (y.val.testBit k.val) else 0) =
      ∑ i : Fin 6, f i.val * bitValue (ZMod 4) ((mixedMask d y.val).testBit i.val) := by
  simp only [mixedPairPosition_small d hd]
  interval_cases d <;> norm_num [Fin.sum_univ_succ] <;>
    fin_cases y <;> norm_num [mixedMask, bit, bitValue, Nat.testBit_eq_decide_div_mod_eq,
      add_assoc]

/-- The natural evaluator retains every phase code, with intrinsic coordinate
zero in the least significant bit of the coordinate mask. -/
theorem fastPhaseExponent_correct (d : Nat) (hd : d ≤ 4)
    (c : Fin (phaseCodeCount d)) (y : Fin 16) :
    ((phaseQuadratic (phaseDecode d c)).eval (fun j : Fin d => y.val.testBit j.val)).val =
      exponent d c.val y.val := by
  have he : (phaseQuadratic (phaseDecode d c)).eval (fun j : Fin d => y.val.testBit j.val) =
      ((selectedDigits 4 (c.val / 2^(d*(d-1)/2)) y.val d +
        2 * selectedDigits 2 c.val (mixedMask d y.val) 6 : Nat) : ZMod 4) := by
    rw [phaseQuadratic_decode_eval_digits]
    simp only [mixedPairList_length_small d hd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      selectedDigits_cast]
    congr 1
    rw [mixedMask_sum d hd y (fun i => (2 : ZMod 4) * (c.val / 2^i % 2 : Nat)),
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, ZMod.val_natCast]
  rfl

theorem fastPhaseExponent_eq_eval (d : Nat) (hd : d ≤ 4)
    (c : Fin (phaseCodeCount d)) (y : Fin 16) :
    exponent d c.val y.val =
      ((phaseQuadratic (phaseDecode d c)).eval (fun j : Fin d => y.val.testBit j.val)).val :=
  (fastPhaseExponent_correct d hd c y).symm

end Holant.Certificates.AffineEndpoint
