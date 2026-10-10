import Holant.Proofs.Recognition.RuntimeEOLiteralRows
import Holant.Proofs.Recognition.RuntimeTensorRequest
import Holant.Proofs.Algorithms.TransformRecognition.RationalDisjunctionMachine

/-! Literal A/P request compilation from original runtime source tables.
The finite class tag selects affine or product templates; their full finite
catalogue, parameter count, original coefficient addresses, pair-view sparse
tables and disjunction are generated internally. One original-root search is
appended, but termination is asserted only by the promised-domain source layer.
No template, transformed coefficient, stopping height or success flag is input.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLiteralRequest
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open UniformTensorWitnessBranch (Metadata metadataEncoding natListEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev Selection := ℕ × (Bool × ℕ)
abbrev selectionEncoding := pairEncoding encodingNatBool RuntimeEOView.viewTailEncoding
abbrev Context := OriginalFamilyPackingMachine.Input × Selection
abbrev contextEncoding := pairEncoding OriginalFamilyPackingMachine.encoding selectionEncoding
abbrev Input := Context × Metadata
abbrev encoding := pairEncoding contextEncoding metadataEncoding

def source (r : Input) : OriginalFamilyPackingMachine.Input := (r.1.1.1,false)
def label (r : Input) : ℕ := r.1.2.1
def complete (r : Input) : Bool := r.1.2.2.1
def layer (r : Input) : ℕ := r.1.2.2.2
def count (r : Input) : ℕ := r.2.1.length
def parameters (product : Bool) (r : Input) : ℕ := if product then 1+2*count r else 1
def allocated (product : Bool) (r : Input) : OriginalAllocatedPackingMachine.Input := (source r,parameters product r)
def width (product : Bool) (r : Input) : ℕ := OriginalAllocatedPackingMachine.width (allocated product r)
def arity (r : Input) : ℕ := ((source r).1.getD (label r) (0,[])).1
def imaginary (product : Bool) (r : Input) : ℕ := 5+parameters product r+(OriginalFamilyPackingMachine.original (source r)).length
def tableInput (product : Bool) (r : Input) : OriginalAddressTablesMachine.Input := ((source r).1,parameters product r,label r)
def base (product : Bool) (r : Input) : RuntimeEOLiteralTable.Base :=
  ((width product r,imaginary product r,imaginary product r+1),
    (arity r,complete r,layer r),r.2,OriginalAddressTablesMachine.table (tableInput product r))
def unary (r : Input) : RationalProductTemplateMachine.Addresses :=
  (List.range (count r)).map (fun j => (6+2*j,7+2*j))
def affineBranches (r : Input) : List RationalDisjunctionMachine.System :=
  (RawAffineEnumeration.templates (count r)).map (fun c => RuntimeEOLiteralRows.affineRows (base false r,5,c))
def productBranches (r : Input) : List RationalDisjunctionMachine.System :=
  (RawProductEnumeration.templates (count r)).map (fun c => RuntimeEOLiteralRows.productRows (base true r,c,5,unary r))
def body (product : Bool) (r : Input) : RationalInputMachine.Body :=
  RationalMatrixMachine.guard (width product r)::
    RationalDisjunctionMachine.combine (width product r) (if product then productBranches r else affineBranches r)
def request (product : Bool) (r : Input) : RationalInputMachine.Input where
  «variables» := width product r
  original := OriginalFamilyPackingMachine.roots (source r)
  body := body product r
  addresses := OriginalAllocatedPackingMachine.addresses (allocated product r)

def context := RuntimeTensorRows.fst contextEncoding metadataEncoding
def metadata := RuntimeTensorRows.snd contextEncoding metadataEncoding
def raw := context.comp (RuntimeTensorRows.fst OriginalFamilyPackingMachine.encoding selectionEncoding)
def selection := context.comp (RuntimeTensorRows.snd OriginalFamilyPackingMachine.encoding selectionEncoding)
def labelExecutes : Executes encoding encodingNatBool label := selection.comp (RuntimeTensorRows.fst encodingNatBool RuntimeEOView.viewTailEncoding)
def mode := selection.comp (RuntimeTensorRows.snd encodingNatBool RuntimeEOView.viewTailEncoding)
def sourceExecutes : Executes encoding OriginalFamilyPackingMachine.encoding source :=
  (raw.comp (Executes.ofComputes OriginalFamilyPackingMachine.family)).pair (RuntimeTensorRows.const encoding encodingBoolBool false)
def countExecutes : Executes encoding encodingNatBool count :=
  (metadata.comp (RuntimeTensorRows.fst natListEncoding RuntimeTensorRows.metadataTailEncoding)).comp
    (RuntimeTensorRows.length encodingNatBool)
def parametersExecutes (product : Bool) : Executes encoding encodingNatBool (parameters product) := by
  cases product
  · exact RuntimeTensorRows.const encoding encodingNatBool 1
  · exact (((RuntimeTensorRows.const encoding encodingNatBool 1).pair
      ((countExecutes.pair countExecutes).comp (Executes.ofComputes RationalInputMachine.Programs.add))).comp
      (Executes.ofComputes RationalInputMachine.Programs.add)).congr (fun r => by dsimp [parameters]; omega)
def allocatedExecutes (product : Bool) : Executes encoding OriginalAllocatedPackingMachine.encoding (allocated product) :=
  sourceExecutes.pair (parametersExecutes product)
def widthExecutes (product : Bool) : Executes encoding encodingNatBool (width product) :=
  (allocatedExecutes product).comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)
def arityExecutes : Executes encoding encodingNatBool arity :=
  (((sourceExecutes.comp (Executes.ofComputes OriginalFamilyPackingMachine.family)).pair labelExecutes).comp
    (RuntimeTensorRows.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))).comp
      (RuntimeTensorRows.fst encodingNatBool CommonFieldMachine.rootsEncoding)
def imaginaryExecutes (product : Bool) : Executes encoding encodingNatBool (imaginary product) :=
  (((RuntimeTensorRows.const encoding encodingNatBool 5).pair (parametersExecutes product)).comp
    (Executes.ofComputes RationalInputMachine.Programs.add)).pair
      (sourceExecutes.comp (Executes.ofComputes OriginalFamilyPackingMachine.originalsCount)) |>.comp
        (Executes.ofComputes RationalInputMachine.Programs.add)
def tableExecutes (product : Bool) : Executes encoding RationalTensorMachine.tableEncoding
    (fun r => OriginalAddressTablesMachine.table (tableInput product r)) :=
  ((sourceExecutes.comp (Executes.ofComputes OriginalFamilyPackingMachine.family)).pair
    ((parametersExecutes product).pair labelExecutes)).comp OriginalAddressTablesMachine.executes

def baseExecutes (product : Bool) : Executes encoding RuntimeEOLiteralTable.baseEncoding (base product) :=
  ((widthExecutes product).pair ((imaginaryExecutes product).pair
    ((imaginaryExecutes product).comp (Executes.ofComputes RationalInputMachine.Programs.successor)))).pair
      ((arityExecutes.pair mode).pair (metadata.pair (tableExecutes product)))

def unaryExecutes : Executes encoding RationalProductTemplateMachine.addressesEncoding unary := by
  let j := RuntimeTensorRows.snd encoding encodingNatBool
  let double := (j.pair j).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let index (k : ℕ) := ((RuntimeTensorRows.const (pairEncoding encoding encodingNatBool) encodingNatBool k).pair double).comp
    (Executes.ofComputes RationalInputMachine.Programs.add)
  let cell : Executes (pairEncoding encoding encodingNatBool) RationalProductTemplateMachine.portsEncoding
      (fun p => (6+2*p.2,7+2*p.2)) :=
    ((index 6).pair (index 7)).congr (fun p => by dsimp; congr 1 <;> omega)
  exact NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalProductTemplateMachine.portsEncoding
    (countExecutes.comp RationalInputMachine.Programs.range) (fun _ j => (6+2*j,7+2*j)) cell

def affineBranchesExecutes : Executes encoding RationalDisjunctionMachine.systemsEncoding affineBranches := by
  let r := RuntimeTensorRows.fst encoding EncodedTable.encoding
  let c := RuntimeTensorRows.snd encoding EncodedTable.encoding
  let prep := (r.comp (baseExecutes false)).pair
    ((RuntimeTensorRows.const (pairEncoding encoding EncodedTable.encoding) encodingNatBool 5).pair c)
  exact NegativeCertificateMachine.Lists.map encoding EncodedTable.encoding RationalSparseMachine.familyEncoding
    (countExecutes.comp RawAffineEnumeration.executes) (fun r c => RuntimeEOLiteralRows.affineRows (base false r,5,c))
    (prep.comp RuntimeEOLiteralRows.affineExecutes)

def productBranchesExecutes : Executes encoding RationalDisjunctionMachine.systemsEncoding productBranches := by
  let r := RuntimeTensorRows.fst encoding RationalProductTemplateMachine.edgesEncoding
  let c := RuntimeTensorRows.snd encoding RationalProductTemplateMachine.edgesEncoding
  let prep := (r.comp (baseExecutes true)).pair (c.pair
    ((RuntimeTensorRows.const (pairEncoding encoding RationalProductTemplateMachine.edgesEncoding) encodingNatBool 5).pair
      (r.comp unaryExecutes)))
  exact NegativeCertificateMachine.Lists.map encoding RationalProductTemplateMachine.edgesEncoding RationalSparseMachine.familyEncoding
    (countExecutes.comp RawProductEnumeration.executes) (fun r c => RuntimeEOLiteralRows.productRows (base true r,c,5,unary r))
    (prep.comp RuntimeEOLiteralRows.productExecutes)

def bodyExecutes (product : Bool) : Executes encoding RationalInputMachine.bodyEncoding (body product) := by
  let branches : Executes encoding RationalDisjunctionMachine.systemsEncoding
      (fun r => if product then productBranches r else affineBranches r) := by
    cases product
    · exact affineBranchesExecutes
    · exact productBranchesExecutes
  let combined := ((widthExecutes product).pair branches).comp RationalDisjunctionMachine.executes
  let guard := (widthExecutes product).comp RationalMatrixMachine.guardExecutes
  exact (guard.pair combined).comp (Executes.ofComputes (StructuralListMachine.consComputes RationalSparseMachine.encoding))

def executes (product : Bool) : Executes encoding RationalInputMachine.encoding (request product) := by
  let raw := (widthExecutes product).pair
    ((sourceExecutes.comp (Executes.ofComputes OriginalFamilyPackingMachine.rootsComputes)).pair
      ((bodyExecutes product).pair ((allocatedExecutes product).comp OriginalAllocatedPackingMachine.addressesExecutes)))
  exact Executes.recode raw id (fun _ => rfl) (fun _ => rfl)

def machine (product : Bool) : BinaryCompose.Machine := (executes product).machine.compose WitnessOutput.originalMachine

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOLiteralRequest
