import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.State
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.ReturningLoop

set_option autoImplicit false

/-! Kernel-checked recovery component. The finite ReturningLoop actually executes all charged
Euclidean blocks and reads each continuation byte. Exactly 2L+4 slots are
available; a pending final state remains pending, not a false infeasibility bit.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
open GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
namespace Body
noncomputable section
def value (s : State) : Bool × State :=
  if s.1=0 then (false,s) else (true,(s.1-1,advance s.2))
def counter : Computes stateEncoding encodingNatBool (fun s : State => s.1) := Wiring.firstComputes _ _
def payload : Computes stateEncoding payloadEncoding (fun s : State => s.2) := Wiring.secondComputes _ _
def exhausted : Computes stateEncoding encodingBoolBool (fun s : State => decide (s.1=0)) :=
  (pairComputes counter (constantComputes stateEncoding encodingNatBool 0)).andThen Endpoints.equalComputes
def decrement : Computes stateEncoding encodingNatBool (fun s : State => s.1-1) :=
  (pairComputes counter (constantComputes stateEncoding encodingNatBool 1)).andThen Endpoints.subtractComputes
def stopped : Computes stateEncoding bodyEncoding (fun s : State => (false,s)) :=
  pairComputes (constantComputes stateEncoding encodingBoolBool false) (identityComputes stateEncoding)
def active : Computes stateEncoding bodyEncoding (fun s : State => (true,(s.1-1,advance s.2))) :=
  pairComputes (constantComputes stateEncoding encodingBoolBool true)
    (pairComputes decrement (payload.andThen advanceComputes))
def core : Computes stateEncoding bodyEncoding value :=
  congrComputes (ifComputes exhausted stopped active) (fun s => by simp [value])
def computes : Computes stateEncoding bodyEncoding value := core.andThen (identityComputes bodyEncoding)
theorem disjoint : computes.machine.output≠computes.machine.input := by intro h; cases h
theorem zero (p : Payload) : value (0,p)=(false,(0,p)) := by simp [value]
theorem successor (r : ℕ) (p : Payload) : value (r+1,p)=(true,(r,advance p)) := by simp [value]
end
end Body
namespace Native
noncomputable section
def machine : Machine := ReturningLoop.machine Body.computes.machine
def ticks : ℕ → Payload → ℕ
  | 0,p => (Body.computes.outputs (0,p)).steps+2*(stateEncoding.encode (0,p)).length+4
  | r+1,p => (Body.computes.outputs (r+1,p)).steps+
      2*(stateEncoding.encode (r,advance p)).length+3+ticks r (advance p)
def ready (s : State) : machine.Config :=
  ReturningLoop.ready Body.computes.machine (.inl Body.computes.machine.main)
    (.inl Body.computes.machine.input) (stateEncoding.encode s)
theorem body_runs (s t : State) (bit : Bool) (he : Body.value s=(bit,t)) :
    Holant.Complexity.StackProtocol.RunsExactly Body.computes.machine.computer.step
      (initList Body.computes.machine.computer (stateEncoding.encode s))
      (haltList Body.computes.machine.computer (Holant.Algebraic.frame [bit]++stateEncoding.encode t))
      (Body.computes.outputs s).steps := by
  let m : Machine := Body.computes.machine
  let n : ℕ := (Body.computes.outputs s).steps
  have h : Holant.Complexity.StackProtocol.RunsExactly m.computer.step
      (initList m.computer (stateEncoding.encode s))
      (haltList m.computer (bodyEncoding.encode (Body.value s))) n :=
    (Body.computes.outputs s).evals_in_steps
  have hb : bodyEncoding.encode (Body.value s) =
      Holant.Algebraic.frame [bit]++stateEncoding.encode t := by
    rw [he]
    rfl
  exact Eq.mp (congrArg
    (fun word : List Bool => Holant.Complexity.StackProtocol.RunsExactly m.computer.step
      (initList m.computer (stateEncoding.encode s)) (haltList m.computer word) n) hb) h
set_option backward.isDefEq.respectTransparency false in
theorem run (r : ℕ) (p : Payload) :
    Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (ready (r,p))
      (haltList machine.computer (stateEncoding.encode (finish r p))) (ticks r p) := by
  induction r generalizing p with
  | zero =>
    exact ReturningLoop.stop_run Body.computes.machine _ _ _
      (body_runs _ _ false (Body.zero p))
  | succ r ih =>
    have h := ReturningLoop.continue_run Body.computes.machine Body.disjoint
      (stateEncoding.encode (r+1,p)) (stateEncoding.encode (r,advance p))
      (Body.computes.outputs (r+1,p)).steps (body_runs _ _ true (Body.successor r p))
    have ht := h.trans (ih (advance p))
    simpa only [ticks,finish,ready,machine,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ht
def outputs (s : State) : TM2OutputsInTime machine.computer (stateEncoding.encode s)
    (some (stateEncoding.encode (finish s.1 s.2))) (ticks s.1 s.2) where
  steps := ticks s.1 s.2
  evals_in_steps := by
    change Holant.Complexity.StackProtocol.RunsExactly machine.computer.step
      (initList machine.computer (stateEncoding.encode s))
      (haltList machine.computer (stateEncoding.encode (finish s.1 s.2))) (ticks s.1 s.2)
    simpa only [machine,ReturningLoop.initial,ready] using run s.1 s.2
  steps_le_m := le_rfl
end
end Native
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
