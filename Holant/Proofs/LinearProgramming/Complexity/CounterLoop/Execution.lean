import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.Semantics

/-! Rational LP physical resource implementation, adapted from the supplied reference.
Exact finite-machine execution of the counter loop, including stop cleanup.
The native controller reads the emitted continuation bit and uses real
copy/move transitions. ticks is explicit structural accounting of actual
body outputs; no choice of a solution or of a whole successful run occurs.
This generic operational termination holds for arbitrary stored query data;
LP meaning and the original-input polynomial bounds are proved separately.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion
open Holant.LocalDrafts.RemoteWork.RationalLP.Optimization Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search
open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
namespace Native
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
noncomputable section

def machine : Machine := ReturningLoop.machine Body.computes.machine

def ticks : ℕ → Bool → StepProgram.Query → ℕ
  | 0,b,q => (Body.computes.outputs (stamp 0 b q)).steps+
      2*(encoding.encode (finish 0 q)).length+4
  | r+1,b,q =>
      if Body.accepted q then (Body.computes.outputs (stamp (r+1) b q)).steps+
        2*(encoding.encode (finish (r+1) q)).length+4
      else if Body.zeroNormal q then (Body.computes.outputs (stamp (r+1) b q)).steps+
        2*(encoding.encode (finish (r+1) q)).length+4
      else (Body.computes.outputs (stamp (r+1) b q)).steps+
        2*(encoding.encode (stamp r false (StepProgram.value q))).length+3+
        ticks r false (StepProgram.value q)

def ready (s : State) : machine.Config :=
  ReturningLoop.ready Body.computes.machine (.inl Body.computes.machine.main)
    (.inl Body.computes.machine.input) (encoding.encode s)

/-- Transport only the returned word; avoid reducing the large composed body. -/
theorem body_runs (s t : State) (bit : Bool) (he : Body.value s=(bit,t)) :
    RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (encoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [bit]++encoding.encode t))
      (Body.computes.outputs s).steps := by
  let m : Machine := Body.computes.machine
  let n : ℕ := (Body.computes.outputs s).steps
  have h : RunsExactly m.computer.step
      (initList m.computer (encoding.encode s))
      (haltList m.computer (bodyEncoding.encode (Body.value s))) n :=
    (Body.computes.outputs s).evals_in_steps
  have hb : bodyEncoding.encode (Body.value s) =
      Holant.Algebraic.frame [bit]++encoding.encode t := by rw [he]; rfl
  exact Eq.mp (congrArg
    (fun word : List Bool => RunsExactly m.computer.step
      (initList m.computer (encoding.encode s)) (haltList m.computer word) n) hb) h

theorem body_stop (s t : State) (he : Body.value s=(false,t)) :
    RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (encoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [false]++encoding.encode t))
      (Body.computes.outputs s).steps := body_runs s t false he

theorem body_continue (s t : State) (he : Body.value s=(true,t)) :
    RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (encoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [true]++encoding.encode t))
      (Body.computes.outputs s).steps := body_runs s t true he

set_option backward.isDefEq.respectTransparency false in
theorem run (r : ℕ) (b : Bool) (q : StepProgram.Query) :
    RunsExactly machine.computer.step (ready (stamp r b q))
      (haltList machine.computer (encoding.encode (finish r q))) (ticks r b q) := by
  induction r generalizing b q with
  | zero =>
    have he : Body.value (stamp 0 b q)=(false,finish 0 q) := by
      rw [Body.zero]
      rfl
    exact ReturningLoop.stop_run Body.computes.machine _ _ _ (body_stop _ _ he)
  | succ r ih =>
    by_cases ha : Body.accepted q
    · have he : Body.value (stamp (r+1) b q)=(false,finish (r+1) q) := by
        rw [Body.accepted_stop _ _ _ ha,finish,if_pos ha]
      simpa only [ticks,ready,machine,if_pos ha] using
        ReturningLoop.stop_run Body.computes.machine _ _ _ (body_stop _ _ he)
    · by_cases hz : Body.zeroNormal q
      · have he : Body.value (stamp (r+1) b q)=(false,finish (r+1) q) := by
          rw [Body.zero_stop _ _ _ ha hz,finish,if_neg ha,if_pos hz]
        simpa only [ticks,ready,machine,if_neg ha,if_pos hz] using
          ReturningLoop.stop_run Body.computes.machine _ _ _ (body_stop _ _ he)
      · have first := ReturningLoop.continue_run Body.computes.machine Body.disjoint
          (encoding.encode (stamp (r+1) b q))
          (encoding.encode (stamp r false (StepProgram.value q)))
          (Body.computes.outputs (stamp (r+1) b q)).steps
          (body_continue _ _ (Body.active r b q ha hz))
        have rest := ih false (StepProgram.value q)
        have both := first.trans rest
        simpa only [ticks,finish,ready,machine,if_neg ha,if_neg hz,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
          using both

/-- This record contains the explicit ticks above, rather than a selected
existential running time. It is for the SAME native loop machine. -/
def outputs (s : State) : TM2OutputsInTime machine.computer (encoding.encode s)
    (some (encoding.encode (finish (remaining s) (query s))))
    (ticks (remaining s) (answer s) (query s)) where
  steps := ticks (remaining s) (answer s) (query s)
  evals_in_steps := by
    change RunsExactly machine.computer.step (initList machine.computer (encoding.encode s))
      (haltList machine.computer (encoding.encode (finish (remaining s) (query s)))) _
    have hs : stamp (remaining s) (answer s) (query s) = s := rfl
    simpa only [machine,ReturningLoop.initial,ready,hs] using
      run (remaining s) (answer s) (query s)
  steps_le_m := le_rfl

end
end Native
end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop
