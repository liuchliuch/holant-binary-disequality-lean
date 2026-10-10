import Holant.Complexity.RationalArithmetic.Normalization
import Holant.Complexity.BinaryArithmetic.EncodedPairing
import Holant.Complexity.BinaryCompose.OutputBound

/-! Canonical rational normalization into the unchanged scalar codec. The
component normalizer and exact natural pairing machine are joined by actual
ordered stack transfer. No rational or pairing operation is a TM instruction. -/
set_option synthInstance.maxSize 4096
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 100000

namespace Holant.Complexity.RationalArithmetic
open Turing Computability BinaryArithmetic BinaryCompose IntegerArithmetic

abbrev pairingMachine : Machine where
  K := EncodedPairing.computer.K
  input := EncodedPairing.computer.k₀
  output := EncodedPairing.computer.k₁
  Label := EncodedPairing.computer.Λ
  main := EncodedPairing.computer.main
  State := EncodedPairing.computer.σ
  initial := EncodedPairing.computer.initialState
  program := EncodedPairing.computer.m

noncomputable def pairingComputes : Computes EncodedAddition.inputEncoding encodingNatBool
    (fun p : ℕ × ℕ => Nat.pair p.1 p.2) where
  machine := pairingMachine
  time := EncodedPairing.pairingPolyTime.time
  outputs p := by
    have h := EncodedPairing.pairingPolyTime.outputsFun p
    change TM2OutputsInTime pairingMachine.computer
      (List.map id (EncodedAddition.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (Nat.pair p.1 p.2)))) _ at h
    simpa only [List.map_id] using h

/-- Reduced component codes stay within a linear bound before exact pairing. -/
theorem normalized_pair_length (n : ℤ) (d : ℕ) :
    (EncodedAddition.inputEncoding.encode
      (Equiv.intEquivNat (mkRat n d).num, (mkRat n d).den)).length ≤
        (fractionEncoding.encode (n,d)).length + 4 := by
  have hout : EncodedAddition.inputEncoding.encode
      (Equiv.intEquivNat (mkRat n d).num, (mkRat n d).den) =
      Holant.Algebraic.frame (normalizeBits (negative n) (encodeNat n.natAbs) (encodeNat d)).1.reverse ++
        (normalizeBits (negative n) (encodeNat n.natAbs) (encodeNat d)).2.reverse := by
    rw [normalizeBits_integer]; rfl
  rw [hout]
  by_cases hd : d = 0
  · subst d
    change 2 ≤ (fractionEncoding.encode (n,0)).length + 4
    omega
  · have hn := Normalization.recode_length_le (negative n) (encodeNat (n.natAbs / Nat.gcd n.natAbs d))
    have hqn := Normalization.quotient_length_le n.natAbs (Nat.gcd n.natAbs d)
    have hqd := Normalization.quotient_length_le d (Nat.gcd n.natAbs d)
    have hm := magnitudeBits_length_le n
    simp only [normalizeBits, encodeNat_eq_nil, hd, ↓reduceIte, GcdBits.gcdBits_encodeNat,
      DivisionBits.divideBits_encodeNat, List.length_append, Holant.Algebraic.frame_length,
      List.length_reverse, fractionEncoding_length]
    omega

noncomputable def normalizedSize : PolynomialOutputBound fractionEncoding EncodedAddition.inputEncoding
    (fun p : ℤ × ℕ => (Equiv.intEquivNat (mkRat p.1 p.2).num, (mkRat p.1 p.2).den)) where
  bound := Polynomial.X + 4
  length_le p := by simpa using normalized_pair_length p.1 p.2

abbrev normalizationMachine : Machine := Normalization.machine.compose pairingMachine

/-- Full finite-machine witness with literal encodeNat(Nat.pair(integerCode,den))
output. In particular a zero fraction produces the nonempty canonical code of 0/1. -/
noncomputable def normalizationComputes : Computes fractionEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℤ × ℕ => mkRat p.1 p.2) := by
  let c := Normalization.computes.comp pairingComputes normalizedSize
  exact { machine := c.machine, time := c.time, outputs := fun p => c.outputs p }

noncomputable def normalizationPolyTime : PolyTime fractionEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℤ × ℕ => mkRat p.1 p.2) := normalizationComputes.toPolyTime

theorem normalization_inFP : InFP fractionEncoding Holant.Algebraic.rationalEncoding
    (fun p : ℤ × ℕ => mkRat p.1 p.2) := normalizationComputes.inFP

/-- Every low-level composition transition also has a fixed primitive budget. -/
theorem normalization_program_budget (label : normalizationMachine.Label) :
    TM2Cost.budget (normalizationMachine.program label) ≤ 12 := by
  change TM2Cost.budget (Machine.composeProgram Normalization.machine pairingMachine label) ≤ 12
  cases label with
  | inl label =>
    exact (Machine.compose_left_budget Normalization.machine pairingMachine label).le.trans
      (Normalization.program_budget label)
  | inr label => cases label with
    | inl label =>
      have h := EncodedPairing.program_budget label
      exact (Machine.compose_right_budget Normalization.machine pairingMachine label).le.trans (h.trans (by decide))
    | inr label => cases label <;> decide

@[simp] theorem normalization_stack_count :
    @Fintype.card normalizationMachine.K normalizationMachine.finiteK = 24 := by decide

@[simp] theorem normalization_label_count :
    @Fintype.card normalizationMachine.Label normalizationMachine.finiteLabel = 84 := by decide

@[simp] theorem normalization_state_count :
    @Fintype.card normalizationMachine.State normalizationMachine.finiteState = 3888 := by decide

end Holant.Complexity.RationalArithmetic
