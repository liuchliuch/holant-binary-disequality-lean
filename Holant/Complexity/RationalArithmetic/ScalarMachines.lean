import Holant.Complexity.RationalArithmetic.EncodedNormalization
import Holant.Complexity.BinaryArithmetic.EncodedUnpairing
import Holant.Complexity.IntegerArithmetic.Addition
import Holant.Complexity.IntegerArithmetic.Multiplication
import Holant.Complexity.BinaryArithmetic.EncodedMultiplication
import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.FixedFieldMachines.Reverse

/-! Faithful scalar-code interfaces. Every codec conversion is an actual bit
reversal or parser/serializer; specifications alone may use literal-word recoding.
These providers expose the same forward framing consumed by fixed-field wiring. -/
set_option synthInstance.maxSize 8192

namespace Holant.Complexity.RationalArithmetic
open Turing Computability BinaryCompose BinaryArithmetic

/-- The outer arithmetic pair keeps both scalar words literally unchanged. -/
abbrev inputEncoding := FixedFieldMachines.pairEncoding Holant.Algebraic.rationalEncoding Holant.Algebraic.rationalEncoding

noncomputable def reversePairComputes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Computes (FixedFieldMachines.pairEncoding ea eb) (FixedFieldMachines.pairEncoding (FixedFieldMachines.reverseEncoding ea) (FixedFieldMachines.reverseEncoding eb)) id :=
  FixedFieldMachines.congrComputes ((FixedFieldMachines.leftMapComputes eb (FixedFieldMachines.reverseComputes ea)).andThen
    (FixedFieldMachines.rightMapComputes (FixedFieldMachines.reverseEncoding ea) (FixedFieldMachines.reverseComputes eb))) (fun _ => rfl)

abbrev integerAdditionMachine : Machine where
  K := IntegerArithmetic.Addition.computer.K
  decidableK := IntegerArithmetic.Addition.computer.kDecidableEq
  finiteK := IntegerArithmetic.Addition.computer.kFin
  input := IntegerArithmetic.Addition.computer.k₀
  output := IntegerArithmetic.Addition.computer.k₁
  Label := IntegerArithmetic.Addition.computer.Λ
  finiteLabel := IntegerArithmetic.Addition.computer.ΛFin
  main := IntegerArithmetic.Addition.computer.main
  State := IntegerArithmetic.Addition.computer.σ
  finiteState := IntegerArithmetic.Addition.computer.σFin
  initial := IntegerArithmetic.Addition.computer.initialState
  program := IntegerArithmetic.Addition.computer.m

abbrev integerMultiplicationMachine : Machine where
  K := IntegerArithmetic.Multiplication.computer.K
  decidableK := IntegerArithmetic.Multiplication.computer.kDecidableEq
  finiteK := IntegerArithmetic.Multiplication.computer.kFin
  input := IntegerArithmetic.Multiplication.computer.k₀
  output := IntegerArithmetic.Multiplication.computer.k₁
  Label := IntegerArithmetic.Multiplication.computer.Λ
  finiteLabel := IntegerArithmetic.Multiplication.computer.ΛFin
  main := IntegerArithmetic.Multiplication.computer.main
  State := IntegerArithmetic.Multiplication.computer.σ
  finiteState := IntegerArithmetic.Multiplication.computer.σFin
  initial := IntegerArithmetic.Multiplication.computer.initialState
  program := IntegerArithmetic.Multiplication.computer.m

abbrev naturalMultiplicationMachine : Machine where
  K := EncodedMultiplication.computer.K
  decidableK := EncodedMultiplication.computer.kDecidableEq
  finiteK := EncodedMultiplication.computer.kFin
  input := EncodedMultiplication.computer.k₀
  output := EncodedMultiplication.computer.k₁
  Label := EncodedMultiplication.computer.Λ
  finiteLabel := EncodedMultiplication.computer.ΛFin
  main := EncodedMultiplication.computer.main
  State := EncodedMultiplication.computer.σ
  finiteState := EncodedMultiplication.computer.σFin
  initial := EncodedMultiplication.computer.initialState
  program := EncodedMultiplication.computer.m

abbrev unpairMachine : Machine where
  K := EncodedUnpairing.computer.K
  decidableK := EncodedUnpairing.computer.kDecidableEq
  finiteK := EncodedUnpairing.computer.kFin
  input := EncodedUnpairing.computer.k₀
  output := EncodedUnpairing.computer.k₁
  Label := EncodedUnpairing.computer.Λ
  finiteLabel := EncodedUnpairing.computer.ΛFin
  main := EncodedUnpairing.computer.main
  State := EncodedUnpairing.computer.σ
  finiteState := EncodedUnpairing.computer.σFin
  initial := EncodedUnpairing.computer.initialState
  program := EncodedUnpairing.computer.m

abbrev natCastMachine : Machine where
  K := Doubling.computer.K
  decidableK := Doubling.computer.kDecidableEq
  finiteK := Doubling.computer.kFin
  input := Doubling.computer.k₀
  output := Doubling.computer.k₁
  Label := Doubling.computer.Λ
  finiteLabel := Doubling.computer.ΛFin
  main := Doubling.computer.main
  State := Doubling.computer.σ
  finiteState := Doubling.computer.σFin
  initial := Doubling.computer.initialState
  program := Doubling.computer.m

noncomputable def integerAdditionReversed :
    Computes (FixedFieldMachines.pairEncoding (FixedFieldMachines.reverseEncoding IntegerArithmetic.encoding)
      (FixedFieldMachines.reverseEncoding IntegerArithmetic.encoding)) IntegerArithmetic.encoding
      (fun p : ℤ × ℤ => p.1 + p.2) where
  machine := integerAdditionMachine
  time := IntegerArithmetic.Addition.additionPolyTime.time
  outputs p := by
    have h := IntegerArithmetic.Addition.additionPolyTime.outputsFun p
    change TM2OutputsInTime integerAdditionMachine.computer
      (List.map id (IntegerArithmetic.pairEncoding.encode p))
      (some (List.map id (IntegerArithmetic.encoding.encode (p.1+p.2)))) _ at h
    simpa only [List.map_id, FixedFieldMachines.pairEncoding, FixedFieldMachines.reverseEncoding, IntegerArithmetic.pairEncoding, EncodedMultiplication.inputEncoding, EncodedAddition.inputEncoding, encodingNatBool] using h

noncomputable def integerMultiplicationReversed :
    Computes (FixedFieldMachines.pairEncoding (FixedFieldMachines.reverseEncoding IntegerArithmetic.encoding)
      (FixedFieldMachines.reverseEncoding IntegerArithmetic.encoding)) IntegerArithmetic.encoding
      (fun p : ℤ × ℤ => p.1 * p.2) where
  machine := integerMultiplicationMachine
  time := IntegerArithmetic.Multiplication.multiplicationPolyTime.time
  outputs p := by
    have h := IntegerArithmetic.Multiplication.multiplicationPolyTime.outputsFun p
    change TM2OutputsInTime integerMultiplicationMachine.computer
      (List.map id (IntegerArithmetic.pairEncoding.encode p))
      (some (List.map id (IntegerArithmetic.encoding.encode (p.1*p.2)))) _ at h
    simpa only [List.map_id, FixedFieldMachines.pairEncoding, FixedFieldMachines.reverseEncoding, IntegerArithmetic.pairEncoding, EncodedMultiplication.inputEncoding, EncodedAddition.inputEncoding, encodingNatBool] using h

noncomputable def naturalMultiplicationReversed :
    Computes (FixedFieldMachines.pairEncoding (FixedFieldMachines.reverseEncoding encodingNatBool) (FixedFieldMachines.reverseEncoding encodingNatBool))
      encodingNatBool (fun p : ℕ × ℕ => p.1 * p.2) where
  machine := naturalMultiplicationMachine
  time := EncodedMultiplication.multiplicationPolyTime.time
  outputs p := by
    have h := EncodedMultiplication.multiplicationPolyTime.outputsFun p
    change TM2OutputsInTime naturalMultiplicationMachine.computer
      (List.map id (EncodedAddition.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1*p.2)))) _ at h
    simpa only [List.map_id, FixedFieldMachines.pairEncoding, FixedFieldMachines.reverseEncoding, IntegerArithmetic.pairEncoding, EncodedMultiplication.inputEncoding, EncodedAddition.inputEncoding, encodingNatBool] using h

noncomputable def integerAdditionComputes :
    Computes (FixedFieldMachines.pairEncoding IntegerArithmetic.encoding IntegerArithmetic.encoding)
      IntegerArithmetic.encoding (fun p : ℤ × ℤ => p.1 + p.2) :=
  FixedFieldMachines.congrComputes ((reversePairComputes _ _).andThen integerAdditionReversed) (fun _ => rfl)

noncomputable def integerMultiplicationComputes :
    Computes (FixedFieldMachines.pairEncoding IntegerArithmetic.encoding IntegerArithmetic.encoding)
      IntegerArithmetic.encoding (fun p : ℤ × ℤ => p.1 * p.2) :=
  FixedFieldMachines.congrComputes ((reversePairComputes _ _).andThen integerMultiplicationReversed) (fun _ => rfl)

noncomputable def naturalMultiplicationComputes :
    Computes (FixedFieldMachines.pairEncoding encodingNatBool encodingNatBool)
      encodingNatBool (fun p : ℕ × ℕ => p.1 * p.2) :=
  FixedFieldMachines.congrComputes ((reversePairComputes _ _).andThen naturalMultiplicationReversed) (fun _ => rfl)

/-- A nonnegative integer's parity code is produced by the one-transition doubler. -/
noncomputable def natCastComputes : Computes encodingNatBool IntegerArithmetic.encoding (fun n : ℕ => (n : ℤ)) where
  machine := natCastMachine
  time := 1
  outputs n := by
    rw [Polynomial.eval_one]
    have h := Doubling.outputs (encodeNat n)
    rw [← IntegerArithmetic.encoding_ofNat] at h
    exact h

/-- The scalar is actually unpaired, and its exact intEquivNat numerator code is
reinterpreted only because it is literally the same component bit string. -/
noncomputable def componentsReversedComputes :
    Computes Holant.Algebraic.rationalEncoding
      (FixedFieldMachines.pairEncoding (FixedFieldMachines.reverseEncoding IntegerArithmetic.encoding) (FixedFieldMachines.reverseEncoding encodingNatBool))
      (fun q : ℚ => (q.num,q.den)) where
  machine := unpairMachine
  time := 6 * Polynomial.X ^ 2 + 22 * Polynomial.X + 9
  outputs q := by
    refine { steps := Unpairing.computeTime (Holant.Algebraic.rationalEncoding.encode q)
             evals_in_steps := EncodedUnpairing.encoded_rational_pair_exact q
             steps_le_m := ?_ }
    simpa using Unpairing.computeTime_le (Holant.Algebraic.rationalEncoding.encode q)

noncomputable def componentsComputes :
    Computes Holant.Algebraic.rationalEncoding (FixedFieldMachines.pairEncoding IntegerArithmetic.encoding encodingNatBool)
      (fun q : ℚ => (q.num,q.den)) :=
  FixedFieldMachines.congrComputes ((componentsReversedComputes.andThen
    (FixedFieldMachines.leftMapComputes (FixedFieldMachines.reverseEncoding encodingNatBool) (FixedFieldMachines.unreverseComputes IntegerArithmetic.encoding))).andThen
      (FixedFieldMachines.rightMapComputes IntegerArithmetic.encoding (FixedFieldMachines.unreverseComputes encodingNatBool))) (fun _ => rfl)

noncomputable def numeratorComputes : Computes Holant.Algebraic.rationalEncoding IntegerArithmetic.encoding Rat.num :=
  FixedFieldMachines.congrComputes (componentsComputes.andThen (FixedFieldMachines.Wiring.firstComputes _ _)) (fun _ => rfl)

noncomputable def denominatorComputes : Computes Holant.Algebraic.rationalEncoding encodingNatBool Rat.den :=
  FixedFieldMachines.congrComputes (componentsComputes.andThen (FixedFieldMachines.Wiring.secondComputes _ _)) (fun _ => rfl)

noncomputable def denominatorIntegerComputes :
    Computes Holant.Algebraic.rationalEncoding IntegerArithmetic.encoding (fun q : ℚ => (q.den : ℤ)) :=
  FixedFieldMachines.congrComputes (denominatorComputes.andThen natCastComputes) (fun _ => rfl)

noncomputable def normalizationReversedComputes :
    Computes (FixedFieldMachines.pairEncoding (FixedFieldMachines.reverseEncoding IntegerArithmetic.encoding) (FixedFieldMachines.reverseEncoding encodingNatBool))
      Holant.Algebraic.rationalEncoding (fun p : ℤ × ℕ => mkRat p.1 p.2) :=
  FixedFieldMachines.recode normalizationComputes id (fun _ => rfl) (fun _ => rfl)

/-- Forward component framing is converted by two real reversal programs before
normalization and exact natural pairing. -/
noncomputable def normalizationForwardComputes :
    Computes (FixedFieldMachines.pairEncoding IntegerArithmetic.encoding encodingNatBool) Holant.Algebraic.rationalEncoding
      (fun p : ℤ × ℕ => mkRat p.1 p.2) :=
  FixedFieldMachines.congrComputes ((reversePairComputes _ _).andThen normalizationReversedComputes) (fun _ => rfl)

end Holant.Complexity.RationalArithmetic
