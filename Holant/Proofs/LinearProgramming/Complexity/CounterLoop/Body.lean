import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.State
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.ReturningLoop

/-! Rational LP physical resource implementation, adapted from the supplied reference.
One physical controller round. Acceptance is tested BEFORE the zero counter:
the last budget center is therefore scanned too. A selected zero normal or
exhausted budget emits false. The live branch runs the same StepProgram and
binary subtraction, and emits a true continuation bit for the native loop.
Eager candidate evaluation, all tests, copying and framing are charged by
body.time. ReturningLoop is reused unchanged, not a host-language while.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators

open Codec
namespace Body
noncomputable section

def accepted (q : StepProgram.Query) : Prop := StepProgram.tags q=[]
def zeroNormal (q : StepProgram.Query) : Prop :=
  StepProgram.normal q=List.replicate q.1.val.dimension 0
instance (q : StepProgram.Query) : Decidable (accepted q) := inferInstanceAs (Decidable (StepProgram.tags q=[]))
instance (q : StepProgram.Query) : Decidable (zeroNormal q) :=
  inferInstanceAs (Decidable (StepProgram.normal q=List.replicate q.1.val.dimension 0))

def stopped (s : State) : Bool × State :=
  (false,stamp (remaining s) (decide (accepted (query s))) (query s))
def advanced (s : State) : Bool × State :=
  (true,stamp (remaining s-1) false (StepProgram.value (query s)))
def value (s : State) : Bool × State :=
  if accepted (query s) then stopped s
  else if zeroNormal (query s) then stopped s
  else if remaining s=0 then stopped s else advanced s

def acceptsComputes : Computes encoding encodingBoolBool
    (fun s : State => decide (accepted (query s))) :=
  (pairComputes (queryComputes.andThen StepProgram.scannerComputes)
    (constantComputes encoding Scanner.answerEncoding [])).andThen
      (equalComputes Scanner.answerEncoding)
def zeroComputes : Computes encoding encodingBoolBool
    (fun s : State => decide (zeroNormal (query s))) :=
  (pairComputes (queryComputes.andThen StepProgram.normalComputes)
    (queryComputes.andThen StepProgram.zeroComputes)).andThen (equalComputes pointEncoding)
def exhaustedComputes : Computes encoding encodingBoolBool (fun s : State => decide (remaining s=0)) :=
  (pairComputes counterComputes (constantComputes encoding encodingNatBool 0)).andThen Endpoints.equalComputes
def decrementComputes : Computes encoding encodingNatBool (fun s : State => remaining s-1) :=
  (pairComputes counterComputes (constantComputes encoding encodingNatBool 1)).andThen Endpoints.subtractComputes

def stoppedComputes : Computes encoding bodyEncoding stopped :=
  pairComputes (constantComputes encoding encodingBoolBool false)
    (pairComputes counterComputes (pairComputes acceptsComputes queryComputes))
def advancedComputes : Computes encoding bodyEncoding advanced :=
  pairComputes (constantComputes encoding encodingBoolBool true)
    (pairComputes decrementComputes
      (pairComputes (constantComputes encoding encodingBoolBool false)
        (queryComputes.andThen StepProgram.computes)))

def core : Computes encoding bodyEncoding value :=
  congrComputes (ifComputes acceptsComputes stoppedComputes
    (ifComputes zeroComputes stoppedComputes
      (ifComputes exhaustedComputes stoppedComputes advancedComputes)))
    (fun s => by simp [value])

/-- A fresh identity suffix makes input/output stack keys disjoint. -/
def computes : Computes encoding bodyEncoding value := core.andThen (identityComputes bodyEncoding)
theorem disjoint : computes.machine.output≠computes.machine.input := by intro h; cases h

@[simp] theorem zero (b : Bool) (q : StepProgram.Query) :
    value (stamp 0 b q)=stopped (stamp 0 b q) := by
  by_cases ha : accepted q <;> by_cases hz : zeroNormal q <;>
    simp [value,remaining,query,stamp,ha,hz]

theorem accepted_stop (r : ℕ) (b : Bool) (q : StepProgram.Query) (ha : accepted q) :
    value (stamp r b q)=(false,stamp r true q) := by
  simp [value,stopped,remaining,query,stamp,ha]

theorem zero_stop (r : ℕ) (b : Bool) (q : StepProgram.Query)
    (ha : ¬accepted q) (hz : zeroNormal q) :
    value (stamp r b q)=(false,stamp r false q) := by
  simp [value,stopped,remaining,query,stamp,ha,hz]

theorem active (r : ℕ) (b : Bool) (q : StepProgram.Query)
    (ha : ¬accepted q) (hz : ¬zeroNormal q) :
    value (stamp (r+1) b q)=(true,stamp r false (StepProgram.value q)) := by
  simp [value,advanced,remaining,query,stamp,ha,hz]

@[simp] theorem flag_false_iff (s : State) :
    (value s).1=false ↔ accepted (query s) ∨ zeroNormal (query s) ∨ remaining s=0 := by
  by_cases ha : accepted (query s) <;> by_cases hz : zeroNormal (query s) <;>
    by_cases hr : remaining s=0 <;> simp [value,stopped,advanced,ha,hz,hr]

end
end Body
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
