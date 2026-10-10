import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.Bounds

/-! Rational LP physical resource implementation, adapted from the supplied reference.
End-to-end n>=2 feasibility branch on ORIGINAL Codec.Input bytes.
The finite machine prepares original state, physically loops, cleans up, and
outputs the actual Boolean. Its polynomial includes preparation and both
composition transfers, all counter/scan/update rounds, and output parsing.
HighInput adds only the legitimate dimension scope and encodes identically
to Codec.inputEncoding: no witness, code, oracle or timeout is inserted.
EO owns dimensions 0/1. Returning true still does not emit Codec.Response.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines Codec
namespace Source
noncomputable section

def stateMachine : Machine := prepare.machine.compose Native.machine
def stateTime : Polynomial ℕ := prepare.time+2*(Bounds.width+1)+Bounds.loopTime

/-- Full original-input operational output. hn is solely the n>=2 branch
condition. No machine correctness or polynomial certificate is an argument. -/
def stateOutput (d : Input) (hn : 2≤d.val.dimension) :
    TM2OutputsInTime stateMachine.computer (inputEncoding.encode d)
      (some (encoding.encode (resultState d))) (stateTime.eval (inputEncoding.encode d).length) := by
  let o := Machine.compose_correct prepare.machine Native.machine _ _ _ _ _
    (prepare.outputs d) (Bounds.outputs d hn)
  refine { steps := o.steps, evals_in_steps := o.evals_in_steps, steps_le_m := o.steps_le_m.trans ?_ }
  have hs := Bounds.initial_length d hn
  simp only [stateTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

abbrev HighInput := {d : Input // 2≤d.val.dimension}
def highEncoding : Encoding HighInput Bool where
  encode d := inputEncoding.encode d.val
  decode bits := do
    let d ← inputEncoding.decode bits
    if h : 2≤d.val.dimension then some ⟨d,h⟩ else none
  decode_encode d := by simp [d.property]

@[simp] theorem original_bytes (d : HighInput) : highEncoding.encode d=inputEncoding.encode d.val := rfl

def stateComputes : Computes highEncoding encoding (fun d : HighInput => resultState d.val) where
  machine := stateMachine
  time := stateTime
  outputs d := stateOutput d.val d.property

def computes : Computes highEncoding encodingBoolBool (fun d : HighInput => result d.val) :=
  stateComputes.andThen answerComputes
def machine : Machine := computes.machine
def time : Polynomial ℕ := computes.time

/-- Root can consume this same machine/time on a dimension-tested original
Input without changing that input's encoding. -/
def output (d : Input) (hn : 2≤d.val.dimension) :
    TM2OutputsInTime machine.computer (inputEncoding.encode d)
      (some (encodingBoolBool.encode (result d))) (time.eval (inputEncoding.encode d).length) :=
  computes.outputs ⟨d,hn⟩

theorem correct (d : HighInput) : result d.val=true ↔ ∃ x, Feasible d.val.val x :=
  CounterLoop.correct d.val d.property

theorem correct_false (d : HighInput) : result d.val=false ↔ ¬∃ x, Feasible d.val.val x := by
  rw [← correct d]
  cases result d.val <;> decide

theorem inFP : InFP highEncoding encodingBoolBool (fun d : HighInput => result d.val) := computes.inFP

def primitivePolynomial : Polynomial ℕ := time*Polynomial.C machine.primitiveBudget
def temporaryPolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial

theorem primitive_cost (d : Input) (hn : 2≤d.val.dimension) :
    primitiveCost machine (output d hn).steps
      (some (initList machine.computer (inputEncoding.encode d)))≤
      primitivePolynomial.eval (inputEncoding.encode d).length := by
  apply (primitiveCost_le _ _ _).trans
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
    Nat.mul_le_mul_right machine.primitiveBudget (output d hn).steps_le_m

theorem temporary_bits (d : Input) (hn : 2≤d.val.dimension) (t : ℕ)
    (ht : t≤(output d hn).steps) (c : machine.Config)
    (hc : (fun p => p.bind machine.computer.step)^[t]
      (some (initList machine.computer (inputEncoding.encode d)))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (inputEncoding.encode d).length := by
  have hs := machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  apply hs.trans
  have hr := Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (output d hn).steps_le_m)
  simpa only [temporaryPolynomial,primitivePolynomial,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left hr (inputEncoding.encode d).length

/-- A physical state-output interface for future exact point recovery. It
returns the SAME terminal state word without selecting a different point. -/
def terminalQueryComputes : Computes highEncoding StepProgram.encoding
    (fun d : HighInput => query (resultState d.val)) := stateComputes.andThen queryComputes

theorem terminal_original (d : HighInput) : (query (resultState d.val)).1=d.val :=
  source_preserved d.val d.property

theorem terminal_thickened (d : HighInput) (ha : result d.val=true) :
    Thickening.At d.val.val (Thickening.epsilon d.val.val)
      (StorageProgram.decode d.val.val.dimension (query (resultState d.val)).2).center :=
  accepted_center d.val d.property ha

end
end Source
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
