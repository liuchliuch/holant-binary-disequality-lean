import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineFamilyEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineAllocationMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAddressTablesMachine
import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineBodyMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineBranchMachine
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Input := OriginalFamilyPackingMachine.Input × RawLocalAffineFamilyEnumeration.Candidate
abbrev encoding := pairEncoding OriginalFamilyPackingMachine.encoding RawLocalAffineFamilyEnumeration.candidateEncoding
abbrev SlotInput := Input × ℕ
abbrev slotEncoding := pairEncoding encoding encodingNatBool

def allocated (r : Input) : OriginalAllocatedPackingMachine.Input :=
  (r.1,LocalAffineAllocationMachine.count r.1.1)
def arityAt (r : Input) (i : ℕ) : ℕ := ((OriginalCatalogueMachine.extended r.1.1).getD i (0,[])).1
def imaginary (r : Input) : ℕ :=
  OriginalAllocatedPackingMachine.base (allocated r)+(OriginalFamilyPackingMachine.original r.1).length

def slot (r : Input) (i : ℕ) : RationalLocalAffineRowsMachine.Input :=
  (((decide (i=r.1.1.length),OriginalAllocatedPackingMachine.width (allocated r),arityAt r i,
    OriginalAddressTablesMachine.table (r.1.1,LocalAffineAllocationMachine.count r.1.1,i)),
    imaginary r,imaginary r+2),
    LocalAffineAllocationMachine.records (r.1.1,i,r.2.getD i []))
def body (r : Input) : List RationalSparseMachine.Poly :=
  RationalMatrixMachine.guard (OriginalAllocatedPackingMachine.width (allocated r)) ::
    RationalAffineBodyMachine.eighthRow (OriginalAllocatedPackingMachine.width (allocated r))
      (imaginary r) (imaginary r+1) (imaginary r+2) ::
    (List.range (r.1.1.length+1)).flatMap (fun i => RationalLocalAffineRowsMachine.rows (slot r i))
def request (r : Input) : RationalInputMachine.Input :=
  ⟨OriginalAllocatedPackingMachine.width (allocated r),OriginalFamilyPackingMachine.roots r.1,
    body r,OriginalAllocatedPackingMachine.addresses (allocated r)⟩

noncomputable section

def source := Wiring.firstComputes OriginalFamilyPackingMachine.encoding RawLocalAffineFamilyEnumeration.candidateEncoding
def family := source.andThen OriginalFamilyPackingMachine.family
def candidate := Wiring.secondComputes OriginalFamilyPackingMachine.encoding RawLocalAffineFamilyEnumeration.candidateEncoding
def familyLength := (family.andThen (WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding)).andThen UnaryBinary.computes

def parameterCount : Executes encoding encodingNatBool (fun r : Input => LocalAffineAllocationMachine.count r.1.1) :=
  (Executes.ofComputes family).comp LocalAffineAllocationMachine.countExecutes

def allocatedExecutes : Executes encoding OriginalAllocatedPackingMachine.encoding allocated :=
  (Executes.ofComputes source).pair parameterCount

def width := allocatedExecutes.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)
def imaginaryExecutes : Executes encoding encodingNatBool imaginary :=
  ((allocatedExecutes.comp (Executes.ofComputes OriginalAllocatedPackingMachine.baseComputes)).pair
    (Executes.ofComputes (source.andThen OriginalFamilyPackingMachine.originalsCount))).comp
      (Executes.ofComputes RationalInputMachine.Programs.add)
def eighth := (imaginaryExecutes.pair
  (Executes.ofComputes (constantComputes encoding encodingNatBool 2))).comp
    (Executes.ofComputes RationalInputMachine.Programs.add)

def context := Wiring.firstComputes encoding encodingNatBool
def index := Wiring.secondComputes encoding encodingNatBool

def arityExecutes : Executes slotEncoding encodingNatBool (fun p : SlotInput => arityAt p.1 p.2) :=
  ((Executes.ofComputes (pairComputes ((context.andThen family).andThen OriginalCatalogueMachine.extendedComputes) index)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))).comp
      (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding))

def edgeFlag : Computes slotEncoding encodingBoolBool (fun p : SlotInput => decide (p.2=p.1.1.1.length)) :=
  (pairComputes index (context.andThen familyLength)).andThen (equalComputes encodingNatBool)

def slotExecutes : Executes slotEncoding RationalLocalAffineRowsMachine.encoding
    (fun p : SlotInput => slot p.1 p.2) := by
  let ctx := Executes.ofComputes context
  let count := ctx.comp parameterCount
  let table := ((Executes.ofComputes (context.andThen family)).pair
    (count.pair (Executes.ofComputes index))).comp OriginalAddressTablesMachine.executes
  let original := (Executes.ofComputes edgeFlag).pair ((ctx.comp width).pair (arityExecutes.pair table))
  let header := original.pair ((ctx.comp imaginaryExecutes).pair (ctx.comp eighth))
  let code := (Executes.ofComputes (pairComputes (context.andThen candidate) index)).comp
    (NegativeCertificateMachine.Lists.lookup RawLocalAffineEnumeration.candidateEncoding [])
  let records := ((Executes.ofComputes (context.andThen family)).pair
    ((Executes.ofComputes index).pair code)).comp LocalAffineAllocationMachine.executes
  exact header.pair records

def eighthExecutes : Executes encoding RationalSparseMachine.encoding
    (fun r : Input => RationalAffineBodyMachine.eighthRow
      (OriginalAllocatedPackingMachine.width (allocated r)) (imaginary r) (imaginary r+1) (imaginary r+2)) := by
  let sqrt := imaginaryExecutes.comp (Executes.ofComputes RationalInputMachine.Programs.successor)
  let vertices := Executes.ofComputes (constantComputes encoding
    RationalAffineBodyMachine.verticesEncoding [])
  let edge := Executes.ofComputes (constantComputes encoding RationalAffineEdgeRowsMachine.blockEncoding
    (0,(0,[],0,[],[]),[]))
  exact (width.pair (imaginaryExecutes.pair (sqrt.pair (eighth.pair (vertices.pair edge))))).comp
    RationalAffineBodyMachine.eighthExecutes

def bodyExecutes : Executes encoding RationalSparseMachine.familyEncoding body := by
  let cells := NegativeCertificateMachine.Lists.map encoding encodingNatBool RationalSparseMachine.familyEncoding
    ((Executes.ofComputes (familyLength.andThen RationalInputMachine.Programs.successor)).comp RationalInputMachine.Programs.range)
    (fun r i => RationalLocalAffineRowsMachine.rows (slot r i)) (slotExecutes.comp RationalLocalAffineRowsMachine.executes)
  let rows := cells.comp (Executes.ofComputes (WireLists.flatten RationalSparseMachine.encoding))
  let withEighth := (eighthExecutes.pair rows).comp
    (Executes.ofComputes (StructuralListMachine.consComputes RationalSparseMachine.encoding))
  let guard := width.comp RationalMatrixMachine.guardExecutes
  exact ((guard.pair withEighth).comp (Executes.ofComputes
    (StructuralListMachine.consComputes RationalSparseMachine.encoding))).congr
      (fun r => by simp only [body,List.flatMap_def,Function.comp_def,id_eq])

def prepare : Executes encoding RationalInputMachine.encoding request := by
  let roots := Executes.ofComputes (source.andThen OriginalFamilyPackingMachine.rootsComputes)
  let addresses := allocatedExecutes.comp OriginalAllocatedPackingMachine.addressesExecutes
  exact Executes.recode (width.pair (roots.pair (bodyExecutes.pair addresses))) id (fun _ => rfl) (fun _ => rfl)
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineBranchMachine
