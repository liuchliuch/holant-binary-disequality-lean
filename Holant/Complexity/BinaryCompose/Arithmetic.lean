import Holant.Complexity.BinaryCompose.OutputBound
import Holant.Complexity.BinaryArithmetic.EncodedAddition
import Holant.Complexity.BinaryArithmetic.EncodedMultiplication
import Holant.Complexity.BinaryArithmetic.Doubling

/-!
# Integrated arithmetic composition examples

The already verified serialized addition and multiplication machines are adapted
without altering their programs. The second component is the genuine in-place
binary doubler. Both the intermediate-size bound and the cost of ordered transfer
are obtained from the general composition theorem.
-/

namespace Holant.Complexity.BinaryCompose
open Turing Computability BinaryArithmetic

abbrev additionMachine : Machine where
  K := EncodedAddition.computer.K
  input := EncodedAddition.computer.k₀
  output := EncodedAddition.computer.k₁
  Label := EncodedAddition.computer.Λ
  main := EncodedAddition.computer.main
  State := EncodedAddition.computer.σ
  initial := EncodedAddition.computer.initialState
  program := EncodedAddition.computer.m

abbrev multiplicationMachine : Machine where
  K := EncodedMultiplication.computer.K
  input := EncodedMultiplication.computer.k₀
  output := EncodedMultiplication.computer.k₁
  Label := EncodedMultiplication.computer.Λ
  main := EncodedMultiplication.computer.main
  State := EncodedMultiplication.computer.σ
  initial := EncodedMultiplication.computer.initialState
  program := EncodedMultiplication.computer.m

abbrev doublingMachine : Machine where
  K := Doubling.computer.K
  input := Doubling.computer.k₀
  output := Doubling.computer.k₁
  Label := Doubling.computer.Λ
  main := Doubling.computer.main
  State := Doubling.computer.σ
  initial := Doubling.computer.initialState
  program := Doubling.computer.m

noncomputable def additionComputes :
    Computes EncodedAddition.inputEncoding encodingNatBool (fun p => p.1 + p.2) where
  machine := additionMachine
  time := EncodedAddition.additionPolyTime.time
  outputs p := by
    have h := EncodedAddition.additionPolyTime.outputsFun p
    change TM2OutputsInTime additionMachine.computer (List.map id (EncodedAddition.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 + p.2)))) _ at h
    simpa only [List.map_id] using h

noncomputable def multiplicationComputes :
    Computes EncodedMultiplication.inputEncoding encodingNatBool (fun p => p.1 * p.2) where
  machine := multiplicationMachine
  time := EncodedMultiplication.multiplicationPolyTime.time
  outputs p := by
    have h := EncodedMultiplication.multiplicationPolyTime.outputsFun p
    change TM2OutputsInTime multiplicationMachine.computer
      (List.map id (EncodedMultiplication.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 * p.2)))) _ at h
    simpa only [List.map_id] using h

noncomputable def doublingComputes : Computes encodingNatBool encodingNatBool (fun n => 2 * n) where
  machine := doublingMachine
  time := 1
  outputs n := by
    rw [Polynomial.eval_one]
    have h := Doubling.outputs (encodeNat n)
    rw [Doubling.shift_encodeNat] at h
    exact h

/-- An actual machine computing twice a sum after physically transferring its
canonical intermediate word into a second in-place arithmetic machine. -/
noncomputable def twiceSumComputes :
    Computes EncodedAddition.inputEncoding encodingNatBool (fun p => 2 * (p.1 + p.2)) :=
  additionComputes.andThen doublingComputes

noncomputable def twiceSumPolyTime :
    PolyTime EncodedAddition.inputEncoding encodingNatBool (fun p => 2 * (p.1 + p.2)) :=
  twiceSumComputes.toPolyTime

/-- A nonlinear arithmetic stage followed by another actual machine. -/
noncomputable def twiceProductComputes :
    Computes EncodedMultiplication.inputEncoding encodingNatBool (fun p => 2 * (p.1 * p.2)) :=
  multiplicationComputes.andThen doublingComputes

noncomputable def twiceProductPolyTime :
    PolyTime EncodedMultiplication.inputEncoding encodingNatBool (fun p => 2 * (p.1 * p.2)) :=
  twiceProductComputes.toPolyTime

/-- Both components alias their own input and output stacks. -/
noncomputable def quadrupleComputes :
    Computes encodingNatBool encodingNatBool (fun n => 2 * (2 * n)) :=
  doublingComputes.andThen doublingComputes

/-- Repeated composition works on already composed machines, using only the
proved output-size bound of the preceding composed program. -/
noncomputable def fourTimesSumComputes :
    Computes EncodedAddition.inputEncoding encodingNatBool (fun p => 2 * (2 * (p.1 + p.2))) :=
  twiceSumComputes.andThen doublingComputes

/-- The two aliased arithmetic components plus transfer have an exact count. -/
theorem quadruple_exact (n : ℕ) :
    (fun p => p.bind (doublingMachine.compose doublingMachine).computer.step)^[
      2 * ((encodeNat (2 * n)).length + 1) + 2]
      (some (initList (doublingMachine.compose doublingMachine).computer (encodeNat n))) =
      some (haltList (doublingMachine.compose doublingMachine).computer (encodeNat (2 * (2 * n)))) := by
  have first : (fun p => p.bind doublingMachine.computer.step)^[1]
      (some (initList doublingMachine.computer (encodeNat n))) =
      some (haltList doublingMachine.computer (encodeNat (2 * n))) := by
    have h := Doubling.step_shift (encodeNat n)
    rw [Doubling.shift_encodeNat] at h
    exact h
  have second : (fun p => p.bind doublingMachine.computer.step)^[1]
      (some (initList doublingMachine.computer (encodeNat (2 * n)))) =
      some (haltList doublingMachine.computer (encodeNat (2 * (2 * n)))) := by
    have h := Doubling.step_shift (encodeNat (2 * n))
    rw [Doubling.shift_encodeNat] at h
    exact h
  have h := Machine.compose_run doublingMachine doublingMachine _ _ _ 1 1 first second
  have hn : 1 + (2 * ((encodeNat (2 * n)).length + 1) + 1) =
      2 * ((encodeNat (2 * n)).length + 1) + 2 := by omega
  rw [hn] at h
  exact h

/-- Complete exact execution of the addition/transfer/doubling program. -/
theorem twiceSum_exact (a b : ℕ) :
    (fun p => p.bind (additionMachine.compose doublingMachine).computer.step)^[
      1 + (2 * ((encodeNat (a + b)).length + 1) +
        ((encodeNat a).length + (encodeNat b).length +
          max (encodeNat a).length (encodeNat b).length + (encodeNat (a + b)).length + 4))]
      (some (initList (additionMachine.compose doublingMachine).computer
        (EncodedAddition.inputEncoding.encode (a, b)))) =
      some (haltList (additionMachine.compose doublingMachine).computer (encodeNat (2 * (a + b)))) := by
  have second : (fun p => p.bind doublingMachine.computer.step)^[1]
      (some (initList doublingMachine.computer (encodeNat (a + b)))) =
      some (haltList doublingMachine.computer (encodeNat (2 * (a + b)))) := by
    have h := Doubling.step_shift (encodeNat (a + b))
    rw [Doubling.shift_encodeNat] at h
    exact h
  exact Machine.compose_run additionMachine doublingMachine _ _ _ _ 1
    (EncodedAddition.encoded_exact a b) second

end Holant.Complexity.BinaryCompose
