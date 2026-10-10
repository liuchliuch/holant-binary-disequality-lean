import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Body

set_option autoImplicit false

/-! Kernel-checked recovery component. Actual finite Boolean-stack ReturningLoop execution,
including continuation headers, output transfer, and clean halt. No host
iteration or existential running time is used as a machine operation.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Native
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose StackProtocol FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.Infrastructure
noncomputable section
attribute [local irreducible] Body.computes
def machine : Machine := ReturningLoop.machine Body.computes.machine
def ticks : ℕ → Payload → ℕ
  | 0,p => (Body.computes.outputs (0,p)).steps+2*(stateEncoding.encode (0,p)).length+4
  | r+1,p => (Body.computes.outputs (r+1,p)).steps+
      2*(stateEncoding.encode (r,advance p)).length+3+ticks r (advance p)
def ready (s : State) : machine.Config :=
  ReturningLoop.ready Body.computes.machine (.inl Body.computes.machine.main)
    (.inl Body.computes.machine.input) (stateEncoding.encode s)
theorem body_word (s t : State) (b : Bool) (he : Body.value s=(b,t)) :
    (fun p => p.bind Body.computes.machine.computer.step)^[(Body.computes.outputs s).steps]
      (some (initList Body.computes.machine.computer (stateEncoding.encode s))) =
      some (haltList Body.computes.machine.computer
        (Holant.Algebraic.frame [b]++stateEncoding.encode t)) := by
  let m : Machine := Body.computes.machine
  let n : ℕ := (Body.computes.outputs s).steps
  have h : (fun p => p.bind m.computer.step)^[n]
      (some (initList m.computer (stateEncoding.encode s))) =
      some (haltList m.computer (bodyEncoding.encode (Body.value s))) :=
    (Body.computes.outputs s).evals_in_steps
  have hword : bodyEncoding.encode (Body.value s)=
      Holant.Algebraic.frame [b]++stateEncoding.encode t := by rw [he]; rfl
  exact Eq.mp (congrArg
    (fun word : List Bool => (fun p => p.bind m.computer.step)^[n]
      (some (initList m.computer (stateEncoding.encode s))) =
      some (haltList m.computer word)) hword) h
set_option backward.isDefEq.respectTransparency false in
theorem run (r : ℕ) (p : Payload) :
    Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (ready (r,p))
      (haltList machine.computer (stateEncoding.encode (finish r p))) (ticks r p) := by
  induction r generalizing p with
  | zero =>
    exact ReturningLoop.stop_run Body.computes.machine
      (stateEncoding.encode (0,p)) (stateEncoding.encode (0,p))
      (Body.computes.outputs (0,p)).steps
      (body_word (0,p) (0,p) false (Body.zero p))
  | succ r ih =>
    have first : Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (ready (r+1,p)) (ready (r,advance p))
        ((Body.computes.outputs (r+1,p)).steps+2*(stateEncoding.encode (r,advance p)).length+3) := by
      simpa only [machine,ready] using
        ReturningLoop.continue_run Body.computes.machine Body.disjoint
          (stateEncoding.encode (r+1,p)) (stateEncoding.encode (r,advance p))
          (Body.computes.outputs (r+1,p)).steps
          (body_word (r+1,p) (r,advance p) true (Body.active r p))
    have joined := first.trans (ih (advance p))
    have htime : ticks r (advance p)+
        ((Body.computes.outputs (r+1,p)).steps+2*(stateEncoding.encode (r,advance p)).length+3)=
        ticks (r+1) p := by
      change _=((Body.computes.outputs (r+1,p)).steps+
        2*(stateEncoding.encode (r,advance p)).length+3)+ticks r (advance p)
      exact Nat.add_comm _ _
    rw [htime] at joined
    exact joined
def outputs (s : State) : TM2OutputsInTime machine.computer (stateEncoding.encode s)
    (some (stateEncoding.encode (finish s.1 s.2))) (ticks s.1 s.2) where
  steps := ticks s.1 s.2
  evals_in_steps := by
    change Holant.Complexity.StackProtocol.RunsExactly machine.computer.step (initList machine.computer (stateEncoding.encode s))
      (haltList machine.computer (stateEncoding.encode (finish s.1 s.2))) _
    have hs : (s.1,s.2) = s := rfl
    simpa only [machine,ReturningLoop.initial,ready,hs] using run s.1 s.2
  steps_le_m := le_rfl
end
end Native
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
