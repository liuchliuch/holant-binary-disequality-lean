import Holant.Proofs.Algorithms.TransformRecognition.RationalTensorMachine
import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineTemplateMachine
import Holant.Proofs.Algorithms.TransformRecognition.SparseProductTemplate


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalProductTemplateMachine
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Edge := (ℕ × ℕ) × Bool
abbrev Addresses := List (ℕ × ℕ)
abbrev Word := RationalTensorMachine.Word
abbrev Input := ℕ × (List Edge × (ℕ × (Addresses × Word)))
abbrev portsEncoding := pairEncoding encodingNatBool encodingNatBool
abbrev edgeEncoding := pairEncoding portsEncoding encodingBoolBool
abbrev edgesEncoding := framedListEncoding edgeEncoding
abbrev addressesEncoding := framedListEncoding portsEncoding
abbrev localEncoding := pairEncoding addressesEncoding RationalTensorMachine.wordEncoding
abbrev scalarTailEncoding := pairEncoding encodingNatBool localEncoding
abbrev tailEncoding := pairEncoding edgesEncoding scalarTailEncoding
abbrev encoding := pairEncoding encodingNatBool tailEncoding

def checkEdge (p : Word × Edge) : Bool :=
  if p.2.2 then p.1.getD p.2.1.1 false == p.1.getD p.2.1.2 false
  else !(p.1.getD p.2.1.1 false == p.1.getD p.2.1.2 false)
def holds (r : Input) : Bool := r.2.1.all (fun e => checkEdge (r.2.2.2.2,e))
def unaryAddress (r : Input) (j : ℕ) : ℕ :=
  if r.2.2.2.2.getD j false then (r.2.2.2.1.getD j (0,0)).2 else (r.2.2.2.1.getD j (0,0)).1
def factors (r : Input) : List RationalSparseMachine.Poly :=
  (List.range r.2.2.2.1.length).map (fun j => RationalSparseMachine.variable r.1 (unaryAddress r j))
def value (r : Input) : RationalSparseMachine.Poly :=
  if holds r then RationalSparseMachine.mul (RationalSparseMachine.variable r.1 r.2.2.1)
    (RationalSparseMachine.product r.1 (factors r)) else []

noncomputable section

def width := Wiring.firstComputes encodingNatBool tailEncoding
def tail := Wiring.secondComputes encodingNatBool tailEncoding
def edges := tail.andThen (Wiring.firstComputes edgesEncoding scalarTailEncoding)
def scalarTail := tail.andThen (Wiring.secondComputes edgesEncoding scalarTailEncoding)
def scalar := scalarTail.andThen (Wiring.firstComputes encodingNatBool localEncoding)
def localData := scalarTail.andThen (Wiring.secondComputes encodingNatBool localEncoding)
def addresses := localData.andThen (Wiring.firstComputes addressesEncoding RationalTensorMachine.wordEncoding)
def word := localData.andThen (Wiring.secondComputes addressesEncoding RationalTensorMachine.wordEncoding)

def checkEdgeExecutes : Executes (pairEncoding RationalTensorMachine.wordEncoding edgeEncoding)
    encodingBoolBool checkEdge := by
  let word := Wiring.firstComputes RationalTensorMachine.wordEncoding edgeEncoding
  let edge := Wiring.secondComputes RationalTensorMachine.wordEncoding edgeEncoding
  let ports := edge.andThen (Wiring.firstComputes portsEncoding encodingBoolBool)
  let flag := edge.andThen (Wiring.secondComputes portsEncoding encodingBoolBool)
  let i := ports.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let j := ports.andThen (Wiring.secondComputes encodingNatBool encodingNatBool)
  let left := (Executes.ofComputes (pairComputes word i)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let right := (Executes.ofComputes (pairComputes word j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let eq := (left.pair right).comp (Executes.ofComputes (equalComputes encodingBoolBool))
  let select := GraphPreprocessing.FiniteRecode.computes
    (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p : Bool × Bool => if p.1 then p.2 else !p.2) 4
    (fun p => by rcases p with ⟨b,c⟩; cases b <;> cases c <;> decide)
  exact ((Executes.ofComputes flag).pair eq).comp (Executes.ofComputes select)

def holdsExecutes : Executes encoding encodingBoolBool holds := by
  let cell := (Executes.ofComputes (pairComputes
    ((Wiring.firstComputes encoding edgeEncoding).andThen word)
    (Wiring.secondComputes encoding edgeEncoding))).comp checkEdgeExecutes
  let checks := NegativeCertificateMachine.Lists.map encoding edgeEncoding encodingBoolBool
    (Executes.ofComputes edges) (fun r e => checkEdge (r.2.2.2.2,e)) cell
  exact (checks.comp (Executes.ofComputes ResidueCells.all)).congr
    (fun r => by simp only [holds,List.all_map,Function.comp_def,id_eq])

def unaryExecutes : Executes (pairEncoding encoding encodingNatBool) encodingNatBool
    (fun p : Input × ℕ => unaryAddress p.1 p.2) := by
  let r := Wiring.firstComputes encoding encodingNatBool
  let j := Wiring.secondComputes encoding encodingNatBool
  let b := (Executes.ofComputes (pairComputes (r.andThen word) j)).comp
    (NegativeCertificateMachine.Lists.lookup encodingBoolBool false)
  let pair := (Executes.ofComputes (pairComputes (r.andThen addresses) j)).comp
    (NegativeCertificateMachine.Lists.lookup portsEncoding (0,0))
  let select := ifComputes (Wiring.firstComputes encodingBoolBool portsEncoding)
    ((Wiring.secondComputes encodingBoolBool portsEncoding).andThen
      (Wiring.secondComputes encodingNatBool encodingNatBool))
    ((Wiring.secondComputes encodingBoolBool portsEncoding).andThen
      (Wiring.firstComputes encodingNatBool encodingNatBool))
  exact (b.pair pair).comp (Executes.ofComputes select)

def factorsExecutes : Executes encoding RationalSparseMachine.familyEncoding factors := by
  let count := (addresses.andThen (WireLists.lengthComputes portsEncoding)).andThen GraphPreprocessing.UnaryBinary.computes
  let cell := ((Executes.ofComputes
    ((Wiring.firstComputes encoding encodingNatBool).andThen width)).pair unaryExecutes).comp
      RationalSparseMachine.variableExecutes
  exact NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalSparseMachine.encoding
    ((Executes.ofComputes count).comp RationalInputMachine.Programs.range)
    (fun r j => RationalSparseMachine.variable r.1 (unaryAddress r j)) cell

def executes : Executes encoding RationalSparseMachine.encoding value := by
  let unaryProduct := ((Executes.ofComputes width).pair factorsExecutes).comp RationalSparseMachine.productExecutes
  let scale := (Executes.ofComputes (pairComputes width scalar)).comp RationalSparseMachine.variableExecutes
  let product := (scale.pair unaryProduct).comp RationalSparseMachine.mulExecutes
  exact (holdsExecutes.pair product).comp (Executes.ofComputes RationalAffineTemplateMachine.select)
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalProductTemplateMachine
