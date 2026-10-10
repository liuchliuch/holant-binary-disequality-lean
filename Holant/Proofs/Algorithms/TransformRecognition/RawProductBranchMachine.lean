import Holant.Proofs.Algorithms.TransformRecognition.RawProductFamilyEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationSource
import Holant.Proofs.Algorithms.TransformRecognition.RationalProductRowsMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawProductBranchMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := OriginalFamilyPackingMachine.Input × RawProductFamilyEnumeration.Candidate
abbrev encoding := pairEncoding OriginalFamilyPackingMachine.encoding RawProductFamilyEnumeration.candidateEncoding
abbrev SlotInput := Input × ℕ
abbrev slotEncoding := pairEncoding encoding encodingNatBool

def allocated (r : Input) : OriginalAllocatedPackingMachine.Input :=
  (r.1,ProductAllocationMachine.count r.1.1)
def arityAt (r : Input) (i : ℕ) : ℕ := ((OriginalCatalogueMachine.extended r.1.1).getD i (0,[])).1
def unaryAddresses (p : SlotInput) : List (ℕ × ℕ) :=
  (List.range (arityAt p.1 p.2)).map (fun j => ProductAllocationMachine.unaryPair
    (ProductAllocationMachine.scalarAddress (p.1.1.1,p.2),j))
def slot (r : Input) (i : ℕ) : RationalProductRowsMachine.Input :=
  ((decide (i=r.1.1.length),OriginalAllocatedPackingMachine.width (allocated r),arityAt r i,
    OriginalAddressTablesMachine.table (r.1.1,ProductAllocationMachine.count r.1.1,i)),
    (if i=r.1.1.length then r.2.2 else r.2.1.getD i []),
    ProductAllocationMachine.scalarAddress (r.1.1,i),unaryAddresses (r,i))
def body (r : Input) : List RationalSparseMachine.Poly :=
  RationalMatrixMachine.guard (OriginalAllocatedPackingMachine.width (allocated r)) ::
    (List.range (r.1.1.length+1)).flatMap (fun i => RationalProductRowsMachine.rows (slot r i))
def request (r : Input) : RationalInputMachine.Input :=
  ⟨OriginalAllocatedPackingMachine.width (allocated r),OriginalFamilyPackingMachine.roots r.1,
    body r,OriginalAllocatedPackingMachine.addresses (allocated r)⟩

noncomputable section
def source := Wiring.firstComputes OriginalFamilyPackingMachine.encoding RawProductFamilyEnumeration.candidateEncoding
def family := source.andThen OriginalFamilyPackingMachine.family
def candidate := Wiring.secondComputes OriginalFamilyPackingMachine.encoding RawProductFamilyEnumeration.candidateEncoding
def familyLength := (family.andThen (WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding)).andThen UnaryBinary.computes
def parameterCount : Executes encoding encodingNatBool (fun r : Input => ProductAllocationMachine.count r.1.1) :=
  (Executes.ofComputes family).comp ProductAllocationMachine.countExecutes
def allocatedExecutes : Executes encoding OriginalAllocatedPackingMachine.encoding allocated :=
  (Executes.ofComputes source).pair parameterCount

def slotContext := Wiring.firstComputes encoding encodingNatBool
def index := Wiring.secondComputes encoding encodingNatBool

def arityExecutes : Executes slotEncoding encodingNatBool (fun p : SlotInput => arityAt p.1 p.2) :=
  ((Executes.ofComputes (pairComputes ((slotContext.andThen family).andThen OriginalCatalogueMachine.extendedComputes) index)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))).comp
      (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding))

def scalarExecutes : Executes slotEncoding encodingNatBool
    (fun p : SlotInput => ProductAllocationMachine.scalarAddress (p.1.1.1,p.2)) :=
  (Executes.ofComputes (pairComputes (slotContext.andThen family) index)).comp ProductAllocationMachine.scalarExecutes

def unariesExecutes : Executes slotEncoding RationalProductTemplateMachine.addressesEncoding unaryAddresses := by
  let cellScalar := (Executes.ofComputes (Wiring.firstComputes slotEncoding encodingNatBool)).comp scalarExecutes
  let j := Executes.ofComputes (Wiring.secondComputes slotEncoding encodingNatBool)
  let cell := (cellScalar.pair j).comp (Executes.ofComputes ProductAllocationMachine.unaryComputes)
  exact NegativeCertificateMachine.Lists.map slotEncoding encodingNatBool RationalProductTemplateMachine.portsEncoding
    (arityExecutes.comp RationalInputMachine.Programs.range)
    (fun p j => ProductAllocationMachine.unaryPair (ProductAllocationMachine.scalarAddress (p.1.1.1,p.2),j)) cell

def edgeFlag : Computes slotEncoding encodingBoolBool (fun p : SlotInput => decide (p.2=p.1.1.1.length)) :=
  (pairComputes index (slotContext.andThen familyLength)).andThen (equalComputes encodingNatBool)

def templateExecutes : Executes slotEncoding RationalProductTemplateMachine.edgesEncoding
    (fun p : SlotInput => if p.2=p.1.1.1.length then p.1.2.2 else p.1.2.1.getD p.2 []) := by
  let codes := slotContext.andThen candidate
  let vertices := codes.andThen (Wiring.firstComputes RawProductEnumeration.outputEncoding RawProductEnumeration.edgesEncoding)
  let edge := codes.andThen (Wiring.secondComputes RawProductEnumeration.outputEncoding RawProductEnumeration.edgesEncoding)
  let vertex := (Executes.ofComputes (pairComputes vertices index)).comp
    (NegativeCertificateMachine.Lists.lookup RawProductEnumeration.edgesEncoding [])
  let pairEncoding := FixedFieldMachines.pairEncoding RawProductEnumeration.edgesEncoding RawProductEnumeration.edgesEncoding
  let choose := ifComputes (Wiring.firstComputes encodingBoolBool pairEncoding)
    ((Wiring.secondComputes encodingBoolBool pairEncoding).andThen
      (Wiring.firstComputes RawProductEnumeration.edgesEncoding RawProductEnumeration.edgesEncoding))
    ((Wiring.secondComputes encodingBoolBool pairEncoding).andThen
      (Wiring.secondComputes RawProductEnumeration.edgesEncoding RawProductEnumeration.edgesEncoding))
  exact (((Executes.ofComputes edgeFlag).pair ((Executes.ofComputes edge).pair vertex)).comp
    (Executes.ofComputes choose)).congr (fun p => by simp only [decide_eq_true_eq]; rfl)

def slotExecutes : Executes slotEncoding RationalProductRowsMachine.encoding
    (fun p : SlotInput => slot p.1 p.2) := by
  let ctx := Executes.ofComputes slotContext
  let width := (ctx.comp allocatedExecutes).comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)
  let count := ctx.comp parameterCount
  let table := ((Executes.ofComputes (slotContext.andThen family)).pair
    (count.pair (Executes.ofComputes index))).comp OriginalAddressTablesMachine.executes
  let original := (Executes.ofComputes edgeFlag).pair (width.pair (arityExecutes.pair table))
  let template := templateExecutes.pair (scalarExecutes.pair unariesExecutes)
  exact original.pair template

def bodyExecutes : Executes encoding RationalSparseMachine.familyEncoding body := by
  let cells := NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalSparseMachine.familyEncoding
    ((Executes.ofComputes (familyLength.andThen RationalInputMachine.Programs.successor)).comp RationalInputMachine.Programs.range)
    (fun r i => RationalProductRowsMachine.rows (slot r i)) (slotExecutes.comp RationalProductRowsMachine.executes)
  let rows := cells.comp (Executes.ofComputes (WireLists.flatten RationalSparseMachine.encoding))
  let guard := (allocatedExecutes.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)).comp
    RationalMatrixMachine.guardExecutes
  exact ((guard.pair rows).comp (Executes.ofComputes
    (StructuralListMachine.consComputes RationalSparseMachine.encoding))).congr
      (fun r => by simp only [body,List.flatMap_def,Function.comp_def,id_eq])

def prepare : Executes encoding RationalInputMachine.encoding request := by
  let width := allocatedExecutes.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)
  let roots := Executes.ofComputes (source.andThen OriginalFamilyPackingMachine.rootsComputes)
  let addresses := allocatedExecutes.comp OriginalAllocatedPackingMachine.addressesExecutes
  exact Executes.recode (width.pair (roots.pair (bodyExecutes.pair addresses))) id (fun _ => rfl) (fun _ => rfl)
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawProductBranchMachine
