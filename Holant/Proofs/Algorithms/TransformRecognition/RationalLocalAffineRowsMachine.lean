import Holant.Proofs.Algorithms.TransformRecognition.RationalLocalTwistMachine
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicLocalAffineRows


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalLocalAffineRowsMachine
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Record := RationalTensorMachine.Word × (Bool × (ℕ × (ℕ × EncodedTable.Data)))
abbrev inverseTailEncoding := pairEncoding encodingNatBool EncodedTable.encoding
abbrev scaleTailEncoding := pairEncoding encodingNatBool inverseTailEncoding
abbrev maskTailEncoding := pairEncoding encodingBoolBool scaleTailEncoding
abbrev recordEncoding := pairEncoding RationalTensorMachine.wordEncoding maskTailEncoding
abbrev recordsEncoding := framedListEncoding recordEncoding
abbrev phaseEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev headerEncoding := pairEncoding RationalSlotTableMachine.encoding phaseEncoding
abbrev Input := (RationalSlotTableMachine.Input × (ℕ × ℕ)) × List Record
abbrev encoding := pairEncoding headerEncoding recordsEncoding
abbrev RecordInput := Input × Record
abbrev recordInputEncoding := pairEncoding encoding recordEncoding
abbrev cellEncoding := pairEncoding recordInputEncoding RationalTensorMachine.wordEncoding

def supportRow (r : Input) (e : Record) : RationalSparseMachine.Poly :=
  let original := RationalSlotTableMachine.polynomial r.1.1 e.1
  if e.2.1 then RationalSparseMachine.sub
    (RationalSparseMachine.mul original (RationalSparseMachine.variable r.1.1.2.1 e.2.2.2.1))
    (RationalSparseMachine.one r.1.1.2.1) else original

def twistRow (r : Input) (e : Record) (x : RationalTensorMachine.Word) : RationalSparseMachine.Poly :=
  RationalSparseMachine.sub
    (RationalSparseMachine.mul (RationalLocalTwistMachine.value (r.1.1.2.1,r.1.2.2,e.1,x))
      (RationalSlotTableMachine.polynomial r.1.1 x))
    (RationalSparseMachine.mul (RationalSparseMachine.variable r.1.1.2.1 e.2.2.1)
      (RationalAffineTemplateMachine.value (r.1.1.2.1,r.1.2.1,e.2.2.2.2,x)))
def twists (r : Input) (e : Record) : List RationalSparseMachine.Poly :=
  if e.2.1 then (RationalTableMachine.words r.1.1.2.2.1).map (twistRow r e) else []
def rows (r : Input) : List RationalSparseMachine.Poly :=
  r.2.map (supportRow r) ++ r.2.flatMap (twists r)

noncomputable section
def header := Wiring.firstComputes headerEncoding recordsEncoding
def records := Wiring.secondComputes headerEncoding recordsEncoding
def slot := header.andThen (Wiring.firstComputes RationalSlotTableMachine.encoding phaseEncoding)
def phase := header.andThen (Wiring.secondComputes RationalSlotTableMachine.encoding phaseEncoding)
def imaginary := phase.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
def eighth := phase.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
def width := slot.andThen RationalSlotTableMachine.width
def arity := slot.andThen RationalSlotTableMachine.arity

def context := Wiring.firstComputes encoding recordEncoding
def record := Wiring.secondComputes encoding recordEncoding
def alpha := record.andThen (Wiring.firstComputes RationalTensorMachine.wordEncoding maskTailEncoding)
def recordTail := record.andThen (Wiring.secondComputes RationalTensorMachine.wordEncoding maskTailEncoding)
def mask := recordTail.andThen (Wiring.firstComputes encodingBoolBool scaleTailEncoding)
def scaleTail := recordTail.andThen (Wiring.secondComputes encodingBoolBool scaleTailEncoding)
def scale := scaleTail.andThen (Wiring.firstComputes encodingNatBool inverseTailEncoding)
def inverseTail := scaleTail.andThen (Wiring.secondComputes encodingNatBool inverseTailEncoding)
def inverse := inverseTail.andThen (Wiring.firstComputes encodingNatBool EncodedTable.encoding)
def affine := inverseTail.andThen (Wiring.secondComputes encodingNatBool EncodedTable.encoding)

def supportExecutes : Executes recordInputEncoding RationalSparseMachine.encoding
    (fun p : RecordInput => supportRow p.1 p.2) := by
  let original := (Executes.ofComputes (pairComputes (context.andThen slot) alpha)).comp
    RationalSlotTableMachine.polynomialExecutes
  let inv := (Executes.ofComputes (pairComputes (context.andThen width) inverse)).comp
    RationalSparseMachine.variableExecutes
  let one := (Executes.ofComputes (context.andThen width)).comp RationalSparseMachine.oneExecutes
  let equation := (((original.pair inv).comp RationalSparseMachine.mulExecutes).pair one).comp
    (Executes.ofComputes RationalSparseMachine.subComputes)
  let choose := ifComputes (Wiring.firstComputes encodingBoolBool RationalSparseMachine.pairEncoding)
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.pairEncoding).andThen
      (Wiring.firstComputes RationalSparseMachine.encoding RationalSparseMachine.encoding))
    ((Wiring.secondComputes encodingBoolBool RationalSparseMachine.pairEncoding).andThen
      (Wiring.secondComputes RationalSparseMachine.encoding RationalSparseMachine.encoding))
  exact ((Executes.ofComputes mask).pair (equation.pair original)).comp (Executes.ofComputes choose)

def twistExecutes : Executes cellEncoding RationalSparseMachine.encoding
    (fun p : RecordInput × RationalTensorMachine.Word => twistRow p.1.1 p.1.2 p.2) := by
  let ctx := Wiring.firstComputes recordInputEncoding RationalTensorMachine.wordEncoding
  let r := ctx.andThen context
  let x := Wiring.secondComputes recordInputEncoding RationalTensorMachine.wordEncoding
  let phaseRequest := pairComputes (r.andThen width)
    (pairComputes (r.andThen eighth) (pairComputes (ctx.andThen alpha) x))
  let twist := (Executes.ofComputes phaseRequest).comp RationalLocalTwistMachine.executes
  let original := (Executes.ofComputes (pairComputes (r.andThen slot) x)).comp
    RationalSlotTableMachine.polynomialExecutes
  let scalar := (Executes.ofComputes (pairComputes (r.andThen width) (ctx.andThen scale))).comp
    RationalSparseMachine.variableExecutes
  let templateRequest := pairComputes (r.andThen width)
    (pairComputes (r.andThen imaginary) (pairComputes (ctx.andThen affine) x))
  let template := (Executes.ofComputes templateRequest).comp RationalAffineTemplateMachine.executes
  let left := (twist.pair original).comp RationalSparseMachine.mulExecutes
  let right := (scalar.pair template).comp RationalSparseMachine.mulExecutes
  exact (left.pair right).comp (Executes.ofComputes RationalSparseMachine.subComputes)

def twistsExecutes : Executes recordInputEncoding RationalSparseMachine.familyEncoding
    (fun p : RecordInput => twists p.1 p.2) := by
  let all := NegativeCertificateMachine.Lists.map recordInputEncoding RationalTensorMachine.wordEncoding
    RationalSparseMachine.encoding
    ((Executes.ofComputes (context.andThen arity)).comp RationalTableMachine.wordsExecutes)
    (fun p x => twistRow p.1 p.2 x) twistExecutes
  let choose := ifComputes (Wiring.firstComputes encodingBoolBool RationalSparseMachine.familyEncoding)
    (Wiring.secondComputes encodingBoolBool RationalSparseMachine.familyEncoding)
    (constantComputes (pairEncoding encodingBoolBool RationalSparseMachine.familyEncoding)
      RationalSparseMachine.familyEncoding [])
  exact ((Executes.ofComputes mask).pair all).comp (Executes.ofComputes choose)

def executes : Executes encoding RationalSparseMachine.familyEncoding rows := by
  let support := NegativeCertificateMachine.Lists.map encoding recordEncoding RationalSparseMachine.encoding
    (Executes.ofComputes records) supportRow supportExecutes
  let twisted := NegativeCertificateMachine.Lists.map encoding recordEncoding RationalSparseMachine.familyEncoding
    (Executes.ofComputes records) twists twistsExecutes
  let flat := twisted.comp (Executes.ofComputes (WireLists.flatten RationalSparseMachine.encoding))
  exact ((support.pair flat).comp (Executes.ofComputes (WireLists.append RationalSparseMachine.encoding))).congr
    (fun r => by simp only [rows,List.flatMap_def])
end

end Holant.LocalDrafts.MainChain.TransformRecognition.RationalLocalAffineRowsMachine
