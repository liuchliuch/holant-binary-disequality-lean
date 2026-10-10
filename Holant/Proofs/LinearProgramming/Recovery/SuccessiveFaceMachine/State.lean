import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.FixProgram

set_option autoImplicit false

/-! Kernel-checked recovery component. Same original/current face bytes, the actual accumulated
canonical scalar list, an actual feasibility flag, and a binary countdown.
Failure is absorbing. No feasible vector or selected minimum is stored as an
initial parameter; every appended word came from the computed scalar Option.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section
abbrev Input := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Source.HighInput
def inputEncoding := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Source.highEncoding
abbrev Payload := Context × (List ℚ × Bool)
def payloadEncoding := Holant.Complexity.FixedFieldMachines.pairEncoding contextEncoding
  (Holant.Complexity.FixedFieldMachines.pairEncoding Codec.pointEncoding Computability.encodingBoolBool)
def context (p : Payload) : Context := p.1
def points (p : Payload) : List ℚ := p.2.1
def alive (p : Payload) : Bool := p.2.2
abbrev Cell := Payload × Option ℚ
def cellEncoding := Holant.Complexity.FixedFieldMachines.pairEncoding payloadEncoding RationalExtraction.Source.scalarEncoding
def cell (p : Payload) : Cell := (p,Scalar.value (context p))
def update (c : Cell) : Payload :=
  if alive c.1 then
    if c.2.isSome then
      ((context c.1).next (c.2.getD 0),points c.1++[c.2.getD 0],true)
    else (context c.1,points c.1,false)
  else c.1
def advance (p : Payload) : Payload := update (cell p)
def initialContext (d : Input) : Context :=
  Context.initial d.val ⟨0,by have hn := d.property; omega⟩
def initialPayload (d : Input) : Payload := (initialContext d,[],(Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value d.val).1)
def «at» (d : Input) : ℕ → Payload
  | 0 => initialPayload d
  | k+1 => advance («at» d k)
abbrev State := ℕ × Payload
def stateEncoding := Holant.Complexity.FixedFieldMachines.pairEncoding Computability.encodingNatBool payloadEncoding
def bodyEncoding := Holant.Complexity.FixedFieldMachines.pairEncoding Computability.encodingBoolBool stateEncoding
def initial (d : Input) : State := (d.val.val.dimension,initialPayload d)
def finish : ℕ → Payload → State
  | 0,p => (0,p)
  | r+1,p => finish r (advance p)
def resultState (d : Input) : State := finish d.val.val.dimension (initialPayload d)
def value (d : Input) : Option (List ℚ) :=
  let p := (resultState d).2
  if alive p then some (points p) else none
theorem finish_exact (d : Input) (k r : ℕ) : finish r («at» d k)=(0,«at» d (k+r)) := by
  induction r generalizing k with
  | zero => rfl
  | succ r ih =>
    change finish r («at» d (k+1))=(0,«at» d (k+(r+1)))
    have hindex : (k+1)+r=k+(r+1) := by omega
    simpa only [hindex] using ih (k+1)
theorem result_exact (d : Input) : resultState d=(0,«at» d d.val.val.dimension) := by
  simpa only [resultState,«at»,Nat.zero_add] using finish_exact d 0 d.val.val.dimension
theorem advance_failed (p : Payload) (hp : alive p=false) : advance p=p := by simp [advance,cell,update,hp]
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
