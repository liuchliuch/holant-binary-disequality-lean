import Holant.Proofs.Algorithms.TransformRecognition.RawProductBranchMachine
import Holant.Proofs.Algorithms.TransformRecognition.RationalDisjunctionMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawProductRecognitionMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := OriginalFamilyPackingMachine.Input
abbrev encoding := OriginalFamilyPackingMachine.encoding

def allocated (r : Input) : OriginalAllocatedPackingMachine.Input := (r,ProductAllocationMachine.count r.1)
def systems (r : Input) : List RationalDisjunctionMachine.System :=
  (RawProductFamilyEnumeration.candidates r.1).map (fun c => RawProductBranchMachine.body (r,c))
def body (r : Input) : RationalDisjunctionMachine.System :=
  RationalMatrixMachine.guard (OriginalAllocatedPackingMachine.width (allocated r)) ::
    RationalDisjunctionMachine.combine (OriginalAllocatedPackingMachine.width (allocated r)) (systems r)
def request (r : Input) : RationalInputMachine.Input :=
  ⟨OriginalAllocatedPackingMachine.width (allocated r),OriginalFamilyPackingMachine.roots r,
    body r,OriginalAllocatedPackingMachine.addresses (allocated r)⟩

noncomputable section
def parameterCount : Executes encoding encodingNatBool (fun r : Input => ProductAllocationMachine.count r.1) :=
  (Executes.ofComputes OriginalFamilyPackingMachine.family).comp ProductAllocationMachine.countExecutes

def allocation : Executes encoding OriginalAllocatedPackingMachine.encoding allocated :=
  (Executes.ofComputes (identityComputes encoding)).pair parameterCount

def systemsExecutes : Executes encoding RationalDisjunctionMachine.systemsEncoding systems :=
  NegativeCertificateMachine.Lists.map encoding RawProductFamilyEnumeration.candidateEncoding
    RationalSparseMachine.familyEncoding
    ((Executes.ofComputes OriginalFamilyPackingMachine.family).comp RawProductFamilyEnumeration.executes)
    (fun r c => RawProductBranchMachine.body (r,c)) RawProductBranchMachine.bodyExecutes

def bodyExecutes : Executes encoding RationalSparseMachine.familyEncoding body := by
  let width := allocation.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)
  let disjunction := (width.pair systemsExecutes).comp RationalDisjunctionMachine.executes
  let guard := width.comp RationalMatrixMachine.guardExecutes
  exact (guard.pair disjunction).comp (Executes.ofComputes (StructuralListMachine.consComputes RationalSparseMachine.encoding))

def prepare : Executes encoding RationalInputMachine.encoding request := by
  let width := allocation.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes)
  let roots := Executes.ofComputes OriginalFamilyPackingMachine.rootsComputes
  let addresses := allocation.comp OriginalAllocatedPackingMachine.addressesExecutes
  exact Executes.recode (width.pair (roots.pair (bodyExecutes.pair addresses))) id (fun _ => rfl) (fun _ => rfl)

def machine := prepare.machine.compose OriginalSystemMachine.machine

def prepared_outputs (r : Input) : TM2OutputsInTime prepare.machine.computer (encoding.encode r)
    (some (RationalInputMachine.encoding.encode (request r))) (prepare.cost r) := prepare.outputs r
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawProductRecognitionMachine
