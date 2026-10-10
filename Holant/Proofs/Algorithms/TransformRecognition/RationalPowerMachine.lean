import Holant.Proofs.Algorithms.TransformRecognition.RationalSparseMachine
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicPhaseCoefficients


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalPowerMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Poly := RationalSparseMachine.Poly
abbrev State := Poly × Poly
abbrev stateEncoding := RationalSparseMachine.pairEncoding
abbrev Input := ℕ × (ℕ × Poly)
abbrev tailEncoding := pairEncoding encodingNatBool RationalSparseMachine.encoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding

def power (n : ℕ) (p : Poly) : ℕ → Poly
  | 0 => RationalSparseMachine.one n
  | k+1 => RationalSparseMachine.mul (power n p k) p
def step (s : State) : State := (s.1,RationalSparseMachine.mul s.2 s.1)
def value (r : Input) : Poly := power r.1 r.2.2 r.2.1

theorem iterate_start (n : ℕ) (p : Poly) (k : ℕ) :
    (step^[k]) (p,RationalSparseMachine.one n) = (p,power n p k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

theorem power_wire {n : ℕ} (p : Sparse.Poly n 1) (k : ℕ) :
    power n (RationalInputMachine.rowWire p) k =
      RationalInputMachine.rowWire (SymbolicPhaseCoefficients.power p k) := by
  induction k with
  | zero => exact RationalSparseMachine.one_wire n
  | succ k ih =>
    rw [power,SymbolicPhaseCoefficients.power,ih,RationalSparseMachine.mul_wire]

noncomputable section

def stepExecutes : Executes stateEncoding stateEncoding step :=
  (Executes.ofComputes (Wiring.firstComputes RationalSparseMachine.encoding RationalSparseMachine.encoding)).pair
    ((Executes.ofComputes (Wiring.swapComputes RationalSparseMachine.encoding RationalSparseMachine.encoding)).comp
      RationalSparseMachine.mulExecutes)

def executes : Executes encoding RationalSparseMachine.encoding value := by
  let n := Wiring.firstComputes encodingNatBool tailEncoding
  let tail := Wiring.secondComputes encodingNatBool tailEncoding
  let k := tail.andThen (Wiring.firstComputes encodingNatBool RationalSparseMachine.encoding)
  let p := tail.andThen (Wiring.secondComputes encodingNatBool RationalSparseMachine.encoding)
  let one := (Executes.ofComputes n).comp RationalSparseMachine.oneExecutes
  let prepare := (Executes.ofComputes k).pair ((Executes.ofComputes p).pair one)
  let loop := CommonFieldMachine.Iteration.executes stateEncoding stepExecutes
  let finish := Executes.ofComputes (Wiring.secondComputes RationalSparseMachine.encoding RationalSparseMachine.encoding)
  exact ((prepare.comp loop).comp finish).congr (fun r => by
    change ((step^[r.2.1]) (r.2.2,RationalSparseMachine.one r.1)).2 = value r
    rw [iterate_start]
    rfl)

def source_outputs {n : ℕ} (p : Sparse.Poly n 1) (k : ℕ) :
    TM2OutputsInTime executes.machine.computer
      (encoding.encode (n,k,RationalInputMachine.rowWire p))
      (some (RationalSparseMachine.encoding.encode
        (RationalInputMachine.rowWire (SymbolicPhaseCoefficients.power p k))))
      (executes.cost (n,k,RationalInputMachine.rowWire p)) := by
  have h := executes.outputs (n,k,RationalInputMachine.rowWire p)
  change TM2OutputsInTime executes.machine.computer _
    (some (RationalSparseMachine.encoding.encode (power n (RationalInputMachine.rowWire p) k))) _ at h
  rw [power_wire] at h
  exact h

theorem primitive_bound (r : Input) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r * executes.machine.primitiveBudget := executes.primitive_bound r

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalPowerMachine
