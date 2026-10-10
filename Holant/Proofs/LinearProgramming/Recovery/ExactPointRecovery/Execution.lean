import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.Body

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
The unchanged finite Boolean-stack ReturningLoop executes every physical
threshold body, reads its actual continuation header, and cleans its output.
ticks is explicit structural accounting of this run, not an existentially
selected running time or a host iterate used as a Turing-machine opcode.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
namespace Native
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
noncomputable section

def machine : Machine := ReturningLoop.machine Body.computes.machine
def ticks : ℕ → Payload → ℕ
  | 0,v => (Body.computes.outputs (stamp 0 v)).steps+2*(encoding.encode (finish 0 v)).length+4
  | r+1,v => (Body.computes.outputs (stamp (r+1) v)).steps+
      2*(encoding.encode (stamp r (advance v))).length+3+ticks r (advance v)
def ready (s : State) : machine.Config :=
  ReturningLoop.ready Body.computes.machine (.inl Body.computes.machine.main)
    (.inl Body.computes.machine.input) (encoding.encode s)

theorem body_runs (s t : State) (bit : Bool) (he : Body.value s=(bit,t)) :
    Holant.Complexity.StackProtocol.RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (encoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [bit]++encoding.encode t))
      (Body.computes.outputs s).steps := by
  let m : Machine := Body.computes.machine
  let n : ℕ := (Body.computes.outputs s).steps
  have h : Holant.Complexity.StackProtocol.RunsExactly m.computer.step
      (initList m.computer (encoding.encode s))
      (haltList m.computer (bodyEncoding.encode (Body.value s))) n :=
    (Body.computes.outputs s).evals_in_steps
  have hb : bodyEncoding.encode (Body.value s)=Holant.Algebraic.frame [bit]++encoding.encode t := by
    rw [he]
    rfl
  exact Eq.mp (congrArg
    (fun word : List Bool => Holant.Complexity.StackProtocol.RunsExactly m.computer.step
      (initList m.computer (encoding.encode s)) (haltList m.computer word) n) hb) h

theorem body_stop (s t : State) (he : Body.value s=(false,t)) :
    Holant.Complexity.StackProtocol.RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (encoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [false]++encoding.encode t))
      (Body.computes.outputs s).steps := body_runs s t false he

theorem body_continue (s t : State) (he : Body.value s=(true,t)) :
    Holant.Complexity.StackProtocol.RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (encoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [true]++encoding.encode t))
      (Body.computes.outputs s).steps := body_runs s t true he

set_option backward.isDefEq.respectTransparency false in
theorem run (r : ℕ) (v : Payload) :
    Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (ready (stamp r v))
      (haltList machine.computer (encoding.encode (finish r v))) (ticks r v) := by
  induction r generalizing v with
  | zero =>
    exact ReturningLoop.stop_run Body.computes.machine _ _ _ (body_stop _ _ (Body.zero v))
  | succ r ih =>
    have first := ReturningLoop.continue_run Body.computes.machine Body.disjoint
      (encoding.encode (stamp (r+1) v)) (encoding.encode (stamp r (advance v)))
      (Body.computes.outputs (stamp (r+1) v)).steps (body_continue _ _ (Body.active r v))
    have both := first.trans (ih (advance v))
    simpa only [ticks,finish,ready,machine,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using both

def outputs (s : State) : TM2OutputsInTime machine.computer (encoding.encode s)
    (some (encoding.encode (finish (remaining s) (payload s)))) (ticks (remaining s) (payload s)) where
  steps := ticks (remaining s) (payload s)
  evals_in_steps := by
    change Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (initList machine.computer (encoding.encode s))
      (haltList machine.computer (encoding.encode (finish (remaining s) (payload s)))) _
    have h := run (remaining s) (payload s)
    have hs : stamp (remaining s) (payload s)=s := rfl
    rw [hs] at h
    simpa only [machine,ReturningLoop.initial,ready] using h
  steps_le_m := le_rfl

end
end Native
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
