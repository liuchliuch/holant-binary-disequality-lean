import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.LengthCounter
import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.PositiveThreshold

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Physical D=2^(2L^2) emission from the original Raw byte stream. The program
counts L physical bits, emits polynomially many unary loop tokens and writes
2L^2 zero bits followed by one. It never loops D times. The composed threshold
compiler has no externally supplied denominator, basis or feasible witness.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.DenominatorProgram
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section

def length : Computes encoding UnaryBinary.unaryEncoding InputBounds.size :=
  (encodeComputes encoding).andThen LengthCounter.computes

def square : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding (fun n => n*n) := by
  let block := (Wiring.firstComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding).andThen
    (WireLists.replicate encodingBoolBool false)
  let blocks := WireLists.tabulate UnaryBinary.unaryEncoding (framedListEncoding encodingBoolBool)
    id (identityComputes UnaryBinary.unaryEncoding) (fun n _ => List.replicate n false) block
  let flat := blocks.andThen (WireLists.flatten encodingBoolBool)
  exact congrComputes (flat.andThen (WireLists.lengthComputes encodingBoolBool))
    (fun n => by simp [List.length_flatten,List.map_map])

def exponent : Computes encoding UnaryBinary.unaryEncoding (fun d => 2*InputBounds.size d^2) :=
  congrComputes ((pairComputes (length.andThen square) (length.andThen square)).andThen
    AccessPrograms.unaryAdd) (fun d => by
      change InputBounds.size d * InputBounds.size d +
        InputBounds.size d * InputBounds.size d = 2 * InputBounds.size d ^ 2
      ring)

def falseWord : Computes UnaryBinary.unaryEncoding Frame.wordEncoding
    (fun n => List.replicate n false) := by
  let bits := (WireLists.replicate encodingBoolBool false).andThen
    (Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Bytecode.flatMap encodingBoolBool
      (fun b => [b]) (encodeComputes encodingBoolBool))
  exact congrComputes bits (fun n => by simp)

theorem encode_power (n : ℕ) : encodingNatBool.encode (2^n) = List.replicate n false ++ [true] := by
  change Computability.encodeNat (2^n) = _
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ,Nat.mul_comm,← BinaryArithmetic.Doubling.shift_encodeNat,ih]
    cases n <;> simp [BinaryArithmetic.Doubling.shift,List.replicate_succ]

def power : Computes UnaryBinary.unaryEncoding encodingNatBool (fun n => 2^n) :=
  recode (joinComputes falseWord
    (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding [true])) id (fun _ => rfl)
      (fun n => (encode_power n).symm)

def computes : Computes encoding encodingNatBool InputBounds.denominator := exponent.andThen power

theorem output_length (d : Raw) : (encodingNatBool.encode (InputBounds.denominator d)).length =
    2*InputBounds.size d^2+1 := by
  rw [InputBounds.denominator,encode_power]
  simp

def coordinateRaw : Computes coordinateEncoding encoding (fun q => q.1.val) :=
  recode (Wiring.firstComputes inputEncoding UnaryBinary.unaryEncoding)
    (fun q => (q.1,q.2.val)) (fun _ => rfl) (fun _ => rfl)

def value (q : CoordinateQuery) : Input :=
  ThresholdProgram.value (q,InputBounds.denominator q.1.val)

/-- Real original-input preprocessing, not a feasibility decision procedure. -/
def thresholdComputes : Computes coordinateEncoding inputEncoding value :=
  (pairComputes (identityComputes coordinateEncoding) (coordinateRaw.andThen computes)).andThen
    ThresholdProgram.validatedComputes

theorem correct (q : CoordinateQuery) : Positive q.1.val q.2 ↔ ∃ y, Feasible (value q).val y :=
  PositiveThreshold.positive_iff_program q.1 q.2

theorem execution (q : CoordinateQuery) :
    StackProtocol.RunsExactly thresholdComputes.machine.computer.step
      (initList thresholdComputes.machine.computer (coordinateEncoding.encode q))
      (haltList thresholdComputes.machine.computer (inputEncoding.encode (value q)))
      (thresholdComputes.outputs q).steps := (thresholdComputes.outputs q).evals_in_steps

theorem time_bound (q : CoordinateQuery) : (thresholdComputes.outputs q).steps ≤
    thresholdComputes.time.eval (coordinateEncoding.encode q).length :=
  (thresholdComputes.outputs q).steps_le_m

theorem output_bound (q : CoordinateQuery) : (inputEncoding.encode (value q)).length ≤
    thresholdComputes.outputBound.bound.eval (coordinateEncoding.encode q).length :=
  thresholdComputes.outputBound.length_le q

theorem primitive_bound (q : CoordinateQuery) :
    primitiveCost thresholdComputes.machine (thresholdComputes.outputs q).steps
      (some (initList thresholdComputes.machine.computer (coordinateEncoding.encode q))) ≤
      (primitivePolynomial thresholdComputes).eval (coordinateEncoding.encode q).length :=
  computes_primitive_cost thresholdComputes q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.DenominatorProgram
