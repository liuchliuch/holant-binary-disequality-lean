import Holant.Proofs.Algorithms.TransformRecognition.RationalSlotTableMachine
import Holant.Proofs.Algorithms.TransformRecognition.RationalProductTemplateSource


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalProductRowsMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Template := List RationalProductTemplateMachine.Edge × (ℕ × RationalProductTemplateMachine.Addresses)
abbrev templateTailEncoding := pairEncoding encodingNatBool RationalProductTemplateMachine.addressesEncoding
abbrev templateEncoding := pairEncoding RationalProductTemplateMachine.edgesEncoding templateTailEncoding
abbrev Input := RationalSlotTableMachine.Input × Template
abbrev encoding := pairEncoding RationalSlotTableMachine.encoding templateEncoding
abbrev cellEncoding := pairEncoding encoding RationalTensorMachine.wordEncoding

def templateRequest (r : Input) (x : RationalTensorMachine.Word) : RationalProductTemplateMachine.Input :=
  (r.1.2.1,r.2.1,r.2.2.1,r.2.2.2,x)
def row (r : Input) (x : RationalTensorMachine.Word) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub (RationalSlotTableMachine.polynomial r.1 x)
    (RationalProductTemplateMachine.value (templateRequest r x))
def rows (r : Input) : List RationalSparseMachine.Poly :=
  (RationalTableMachine.words r.1.2.2.1).map (row r)

noncomputable section
def slot := Wiring.firstComputes RationalSlotTableMachine.encoding templateEncoding
def template := Wiring.secondComputes RationalSlotTableMachine.encoding templateEncoding
def edges := template.andThen (Wiring.firstComputes RationalProductTemplateMachine.edgesEncoding templateTailEncoding)
def templateTail := template.andThen (Wiring.secondComputes RationalProductTemplateMachine.edgesEncoding templateTailEncoding)
def scalar := templateTail.andThen (Wiring.firstComputes encodingNatBool RationalProductTemplateMachine.addressesEncoding)
def unaries := templateTail.andThen (Wiring.secondComputes encodingNatBool RationalProductTemplateMachine.addressesEncoding)

def cell : Executes cellEncoding RationalSparseMachine.encoding
    (fun p : Input × RationalTensorMachine.Word => row p.1 p.2) := by
  let ctx := Wiring.firstComputes encoding RationalTensorMachine.wordEncoding
  let x := Wiring.secondComputes encoding RationalTensorMachine.wordEncoding
  let original := (Executes.ofComputes (pairComputes (ctx.andThen slot) x)).comp
    RationalSlotTableMachine.polynomialExecutes
  let request := pairComputes ((ctx.andThen slot).andThen RationalSlotTableMachine.width)
    (pairComputes (ctx.andThen edges) (pairComputes (ctx.andThen scalar) (pairComputes (ctx.andThen unaries) x)))
  let value := (Executes.ofComputes request).comp RationalProductTemplateMachine.executes
  exact (original.pair value).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def executes : Executes encoding RationalSparseMachine.familyEncoding rows :=
  NegativeCertificateMachine.Lists.map encoding RationalTensorMachine.wordEncoding RationalSparseMachine.encoding
    ((Executes.ofComputes (slot.andThen RationalSlotTableMachine.arity)).comp RationalTableMachine.wordsExecutes)
    row cell
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalProductRowsMachine
