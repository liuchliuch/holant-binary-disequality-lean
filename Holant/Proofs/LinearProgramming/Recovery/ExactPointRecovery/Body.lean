import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.State
import Holant.Proofs.LinearProgramming.Recovery.Infrastructure.ReturningLoop

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
Physical binary countdown and one midpoint request. The actual receipt bit
selects one binary numerator; both candidates and every eager conditional
subprogram are included in computes.time. A zero remaining counter emits
false continuation and retains the already isolated interval, not false LP.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
namespace Body
noncomputable section

def stopped (s : State) : Bool × State := (false,s)
def advanced (s : State) : Bool × State := (true,stamp (remaining s-1) (advance (payload s)))
def value (s : State) : Bool × State := if remaining s=0 then stopped s else advanced s
def exhaustedComputes : Computes encoding encodingBoolBool (fun s : State => decide (remaining s=0)) :=
  (pairComputes counterComputes (constantComputes encoding encodingNatBool 0)).andThen Endpoints.equalComputes
def decrementComputes : Computes encoding encodingNatBool (fun s : State => remaining s-1) :=
  (pairComputes counterComputes (constantComputes encoding encodingNatBool 1)).andThen Endpoints.subtractComputes
def stoppedComputes : Computes encoding bodyEncoding stopped :=
  pairComputes (constantComputes encoding encodingBoolBool false) (identityComputes encoding)
def advancedComputes : Computes encoding bodyEncoding advanced :=
  pairComputes (constantComputes encoding encodingBoolBool true)
    (pairComputes decrementComputes (payloadComputes.andThen advanceComputes))
def core : Computes encoding bodyEncoding value :=
  congrComputes (ifComputes exhaustedComputes stoppedComputes advancedComputes) (fun s => by simp [value])
def computes : Computes encoding bodyEncoding value := core.andThen (identityComputes bodyEncoding)
theorem disjoint : computes.machine.output≠computes.machine.input := by intro h; cases h

@[simp] theorem zero (v : Payload) : value (stamp 0 v)=(false,stamp 0 v) := by
  simp [value,stopped,remaining,stamp]
theorem active (r : ℕ) (v : Payload) :
    value (stamp (r+1) v)=(true,stamp r (advance v)) := by
  simp [value,advanced,remaining,payload,stamp]
theorem flag_false_iff (s : State) : (value s).1=false ↔ remaining s=0 := by
  by_cases h : remaining s=0 <;> simp [value,stopped,advanced,h]

end
end Body
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
