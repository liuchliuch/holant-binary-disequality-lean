import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Programs
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.ReturningLoop

set_option autoImplicit false

/-! Kernel-checked recovery component. Physical binary countdown. Every active round runs the
actual interval/Euclid/fixed-row/list program. Eager candidate computations on
the stop or absorbing failure branch remain charged by computes.time.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Body
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
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
def continued : Computes stateEncoding bodyEncoding (fun s : State => (true,(s.1-1,advance s.2))) :=
  pairComputes (constantComputes stateEncoding encodingBoolBool true)
    (pairComputes decrement (payload.andThen Programs.advanceComputes))
def core : Computes stateEncoding bodyEncoding value :=
  congrComputes (ifComputes exhausted stopped continued) (fun s => by simp [value])
def computes : Computes stateEncoding bodyEncoding value := core.andThen (identityComputes bodyEncoding)
theorem disjoint : computes.machine.output≠computes.machine.input := by intro h; cases h
@[simp] theorem zero (p : Payload) : value (0,p)=(false,(0,p)) := by simp [value]
theorem active (r : ℕ) (p : Payload) : value (r+1,p)=(true,(r,advance p)) := by simp [value]
end
end Body
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
