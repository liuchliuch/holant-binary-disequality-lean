import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Execution

set_option autoImplicit false

/-! Kernel-checked recovery component. Every physical Euclidean block has time, output and all
temporary-stack bounds in its actual binary input word. The first initialized
block has these bounds in the ORIGINAL endpoint/cap word. The bounded loop has
explicit aggregate ticks and storage, but a uniform original-word polynomial
for the entire loop is separately supplied by GlobalBounds.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Bounds
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
noncomputable section

def blockValue (q : Query) : Result := (advance (q,Initialize.value q)).2
def blockComputes : Computes queryEncoding resultEncoding blockValue :=
  ((pairComputes (identityComputes queryEncoding) Initialize.computes).andThen advanceComputes).andThen
    (Wiring.secondComputes _ _)
def blockTime : Polynomial ℕ := blockComputes.time
def blockWord : Polynomial ℕ := blockComputes.outputBound.bound
def blockPrimitive : Polynomial ℕ := primitivePolynomial blockComputes
def blockTemporary : Polynomial ℕ := Polynomial.X+blockPrimitive

theorem step_execution (p : StepInput) :
    StackProtocol.RunsExactly Programs.computes.machine.computer.step
      (initList Programs.computes.machine.computer (stepEncoding.encode p))
      (haltList Programs.computes.machine.computer (resultEncoding.encode (Jump.step p)))
      (Programs.computes.outputs p).steps := (Programs.computes.outputs p).evals_in_steps
theorem step_time (p : StepInput) : (Programs.computes.outputs p).steps≤
    Programs.computes.time.eval (stepEncoding.encode p).length := (Programs.computes.outputs p).steps_le_m
theorem step_word (p : StepInput) : (resultEncoding.encode (Jump.step p)).length≤
    Programs.computes.outputBound.bound.eval (stepEncoding.encode p).length :=
  Programs.computes.outputBound.length_le p
theorem step_primitive (p : StepInput) :
    primitiveCost Programs.computes.machine (Programs.computes.outputs p).steps
      (some (initList Programs.computes.machine.computer (stepEncoding.encode p)))≤
        (primitivePolynomial Programs.computes).eval (stepEncoding.encode p).length :=
  computes_primitive_cost Programs.computes p
theorem step_temporary (p : StepInput) (t : ℕ) (ht : t≤(Programs.computes.outputs p).steps)
    (c : Programs.computes.machine.Config)
    (hc : (fun s => s.bind Programs.computes.machine.computer.step)^[t]
      (some (initList Programs.computes.machine.computer (stepEncoding.encode p)))=some c) :
    stackSize c.stk≤(stepEncoding.encode p).length+
      Programs.computes.time.eval (stepEncoding.encode p).length*Programs.computes.machine.primitiveBudget := by
  have hs := Programs.computes.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (ht.trans (step_time p))) _)

theorem block_safe (q : Query) (hq : Valid q) : Jump.Safe q (blockValue q) := by
  simpa only [blockValue,advance_source] using advance_safe (q,Initialize.value q) hq (Initialize.safe q hq)
theorem block_execution (q : Query) :
    StackProtocol.RunsExactly blockComputes.machine.computer.step
      (initList blockComputes.machine.computer (queryEncoding.encode q))
      (haltList blockComputes.machine.computer (resultEncoding.encode (blockValue q)))
      (blockComputes.outputs q).steps := (blockComputes.outputs q).evals_in_steps
theorem block_time (q : Query) : (blockComputes.outputs q).steps≤
    blockTime.eval (queryEncoding.encode q).length := (blockComputes.outputs q).steps_le_m
theorem block_word (q : Query) : (resultEncoding.encode (blockValue q)).length≤
    blockWord.eval (queryEncoding.encode q).length := blockComputes.outputBound.length_le q
theorem block_primitive (q : Query) :
    primitiveCost blockComputes.machine (blockComputes.outputs q).steps
      (some (initList blockComputes.machine.computer (queryEncoding.encode q)))≤
        blockPrimitive.eval (queryEncoding.encode q).length := computes_primitive_cost blockComputes q
theorem block_temporary (q : Query) (t : ℕ) (ht : t≤(blockComputes.outputs q).steps)
    (c : blockComputes.machine.Config)
    (hc : (fun s => s.bind blockComputes.machine.computer.step)^[t]
      (some (initList blockComputes.machine.computer (queryEncoding.encode q)))=some c) :
    stackSize c.stk≤blockTemporary.eval (queryEncoding.encode q).length := by
  have hs := blockComputes.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  apply hs.trans
  simpa only [blockTemporary,blockPrimitive,blockTime,primitivePolynomial,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right blockComputes.machine.primitiveBudget (ht.trans (block_time q))) _

/-- Original bytes physically produce the whole linear slot budget. -/
theorem slot_count (q : Query) : rounds q=2*(queryEncoding.encode q).length+4 := rfl
theorem slot_count_bound (q : Query) : rounds q≤
    countUnary.outputBound.bound.eval (queryEncoding.encode q).length := by
  have h := countUnary.outputBound.length_le q
  simpa [GraphPreprocessing.UnaryBinary.unaryEncoding] using h
theorem body_time (s : State) : (Body.computes.outputs s).steps≤
    Body.computes.time.eval (stateEncoding.encode s).length := (Body.computes.outputs s).steps_le_m
theorem body_word (s : State) : (bodyEncoding.encode (Body.value s)).length≤
    Body.computes.outputBound.bound.eval (stateEncoding.encode s).length :=
  Body.computes.outputBound.length_le s
theorem body_primitive (s : State) :
    primitiveCost Body.computes.machine (Body.computes.outputs s).steps
      (some (initList Body.computes.machine.computer (stateEncoding.encode s)))≤
        (primitivePolynomial Body.computes).eval (stateEncoding.encode s).length :=
  computes_primitive_cost Body.computes s
theorem loop_primitive (s : State) :
    primitiveCost Native.machine (Native.outputs s).steps
      (some (initList Native.machine.computer (stateEncoding.encode s)))≤
        Native.ticks s.1 s.2*Native.machine.primitiveBudget := primitiveCost_le _ _ _
theorem loop_temporary (s : State) (t : ℕ) (ht : t≤(Native.outputs s).steps)
    (c : Native.machine.Config)
    (hc : (fun p => p.bind Native.machine.computer.step)^[t]
      (some (initList Native.machine.computer (stateEncoding.encode s)))=some c) :
    stackSize c.stk≤(stateEncoding.encode s).length+
      Native.ticks s.1 s.2*Native.machine.primitiveBudget := by
  have hs := Native.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) _)

end
end Bounds
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
