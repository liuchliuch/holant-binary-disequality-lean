import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.Monotone

set_option autoImplicit false

/-! Kernel-checked recovery component. Runtime fields are the original system and current
coordinate query. Erased proof fields assert only equal dimensions and word
monotonicity, with initialization/fixation producers here. No optimum,
feasible point, successful search, Supporting certificate or solver is input.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines Codec
noncomputable section

structure Context where
  original : Codec.Input
  current : CoordinateQuery
  sameDimension : current.1.val.dimension=original.val.dimension
  sourceSize : InputBounds.size original.val≤InputBounds.size current.1.val
abbrev ContextWire := Codec.Input × CoordinateQuery
def contextWireEncoding := pairEncoding inputEncoding coordinateEncoding
def Context.wire (c : Context) : ContextWire := (c.original,c.current)
def contextEncoding : Encoding Context Bool where
  encode c := contextWireEncoding.encode c.wire
  decode bits := do
    let (d,q) ← contextWireEncoding.decode bits
    if h : q.1.val.dimension=d.val.dimension ∧ InputBounds.size d.val≤InputBounds.size q.1.val then
      some ⟨d,q,h.1,h.2⟩ else none
  decode_encode c := by simp [Context.wire,c.sameDimension,c.sourceSize]
def Context.initial (d : Codec.Input) (j : Fin d.val.dimension) : Context := ⟨d,⟨d,j⟩,rfl,le_rfl⟩
def Context.fix (c : Context) (r : ℚ) : Context :=
  let next := ExactPointRecovery.ThresholdProgram.fixedValue (c.current,r.num.toNat,r.den)
  ⟨c.original,⟨next,c.current.2⟩,c.sameDimension,
    c.sourceSize.trans (Monotone.fixed_size c.current r.num.toNat r.den)⟩
def project (c : Context) (x : Fin c.current.1.val.dimension → ℚ) : Fin c.original.val.dimension → ℚ :=
  fun j => x (Fin.cast c.sameDimension.symm j)

namespace ContextProgram
noncomputable section
def original : Computes contextEncoding inputEncoding Context.original :=
  recode (Wiring.firstComputes inputEncoding coordinateEncoding) Context.wire (fun _ => rfl) (fun _ => rfl)
def current : Computes contextEncoding coordinateEncoding Context.current :=
  recode (Wiring.secondComputes inputEncoding coordinateEncoding) Context.wire (fun _ => rfl) (fun _ => rfl)
def originalRaw : Computes contextEncoding Codec.encoding (fun c : Context => c.original.val) :=
  recode original id (fun _ => rfl) (fun _ => rfl)
def currentInput : Computes contextEncoding inputEncoding (fun c : Context => c.current.1) :=
  current.andThen ExactPointRecovery.ThresholdProgram.coordinateInput
def currentRaw : Computes contextEncoding Codec.encoding (fun c : Context => c.current.1.val) :=
  recode currentInput id (fun _ => rfl) (fun _ => rfl)
end
end ContextProgram
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
