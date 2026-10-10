import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.State

set_option autoImplicit false

/-! Kernel-checked recovery component. One actual scalar call produces one Cell word, then all
Option/row/list/flag operations consume THAT word. Original Receipt initializes
the feasibility bit; its returned thickened center is never used as a seed.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Programs
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators FixedGadgetSubstitution.Compiler
noncomputable section
def contextComputes : Computes payloadEncoding contextEncoding context := Wiring.firstComputes _ _
def restComputes : Computes payloadEncoding (pairEncoding Codec.pointEncoding encodingBoolBool)
    (fun p : Payload => p.2) := Wiring.secondComputes _ _
def pointsComputes : Computes payloadEncoding Codec.pointEncoding points := restComputes.andThen (Wiring.firstComputes _ _)
def aliveComputes : Computes payloadEncoding encodingBoolBool alive := restComputes.andThen (Wiring.secondComputes _ _)
def cellComputes : Computes payloadEncoding cellEncoding cell :=
  pairComputes (identityComputes payloadEncoding) (contextComputes.andThen Scalar.computes)
def cellPayload : Computes cellEncoding payloadEncoding (fun c : Cell => c.1) := Wiring.firstComputes _ _
def cellOption : Computes cellEncoding RationalExtraction.Source.scalarEncoding (fun c : Cell => c.2) := Wiring.secondComputes _ _
def present : Computes cellEncoding encodingBoolBool (fun c : Cell => c.2.isSome) := cellOption.andThen OptionCell.present
def selected : Computes cellEncoding rationalEncoding (fun c : Cell => c.2.getD 0) := cellOption.andThen OptionCell.scalar
def cellContext := cellPayload.andThen contextComputes
def cellPoints := cellPayload.andThen pointsComputes
def cellAlive := cellPayload.andThen aliveComputes
def nextContext : Computes cellEncoding contextEncoding (fun c : Cell => (context c.1).next (c.2.getD 0)) :=
  (pairComputes cellContext selected).andThen FixProgram.computes
def nextPoints : Computes cellEncoding Codec.pointEncoding (fun c : Cell => points c.1++[c.2.getD 0]) :=
  (pairComputes cellPoints
    (fixedListComputes cellEncoding rationalEncoding (fun c (_ : Unit) => c.2.getD 0)
      (fun _ => selected) [()])).andThen (WireLists.append rationalEncoding)
def succeeded : Computes cellEncoding payloadEncoding
    (fun c : Cell => ((context c.1).next (c.2.getD 0),points c.1++[c.2.getD 0],true)) :=
  pairComputes nextContext (pairComputes nextPoints (constantComputes cellEncoding encodingBoolBool true))
def failed : Computes cellEncoding payloadEncoding (fun c : Cell => (context c.1,points c.1,false)) :=
  pairComputes cellContext (pairComputes cellPoints (constantComputes cellEncoding encodingBoolBool false))
def updateComputes : Computes cellEncoding payloadEncoding update :=
  congrComputes (ifComputes cellAlive (ifComputes present succeeded failed) cellPayload)
    (fun c => by simp [update])
def advanceComputes : Computes payloadEncoding payloadEncoding advance := cellComputes.andThen updateComputes

def originalInput : Computes inputEncoding Codec.inputEncoding (fun d : Input => d.val) :=
  recode (identityComputes Codec.inputEncoding) Subtype.val (fun _ => rfl) (fun _ => rfl)
def initialContextComputes : Computes inputEncoding contextEncoding initialContext :=
  recode (pairComputes originalInput
    (pairComputes originalInput (constantComputes inputEncoding UnaryBinary.unaryEncoding 0))) id
      (fun _ => rfl) (fun _ => rfl)
def originalReceipt : Computes inputEncoding Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.encoding
    (fun d : Input => Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value d.val) := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.computes
def originalAlive : Computes inputEncoding encodingBoolBool
    (fun d : Input => (Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value d.val).1) :=
  originalReceipt.andThen (Wiring.firstComputes _ _)
def initialPayloadComputes : Computes inputEncoding payloadEncoding initialPayload :=
  pairComputes initialContextComputes
    (pairComputes (constantComputes inputEncoding Codec.pointEncoding []) originalAlive)
def originalRaw : Computes inputEncoding Codec.encoding (fun d : Input => d.val.val) :=
  recode originalInput id (fun _ => rfl) (fun _ => rfl)
def countUnary : Computes inputEncoding UnaryBinary.unaryEncoding (fun d : Input => d.val.val.dimension) :=
  originalRaw.andThen Parsing.dimension
def countBinary : Computes inputEncoding encodingNatBool (fun d : Input => d.val.val.dimension) :=
  countUnary.andThen UnaryBinary.computes
def prepare : Computes inputEncoding stateEncoding initial := pairComputes countBinary initialPayloadComputes
end
end Programs
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
