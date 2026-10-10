import Holant.Proofs.Algorithms.TransformRecognition.RawAffineFamilyEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumerationValidity
import Holant.Proofs.Algorithms.TransformRecognition.RationalDisjunctionMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineRecognitionMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Input := OriginalFamilyPackingMachine.Input
abbrev encoding := OriginalFamilyPackingMachine.encoding

def branchSystems (r : Input) : List RationalDisjunctionMachine.System :=
  (RawAffineFamilyEnumeration.candidates r.1).map
    (fun t => RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput (r,t)))
def body (r : Input) : RationalDisjunctionMachine.System :=
  RationalMatrixMachine.guard (OriginalFamilyPackingMachine.width r) ::
    RationalDisjunctionMachine.combine (OriginalFamilyPackingMachine.width r) (branchSystems r)
def request (r : Input) : RationalInputMachine.Input :=
  ⟨OriginalFamilyPackingMachine.width r,OriginalFamilyPackingMachine.roots r,
    body r,OriginalFamilyPackingMachine.addresses r⟩

noncomputable section

def branchCell : Executes
    (pairEncoding encoding RawAffineBranchMachine.templatesEncoding)
    RationalSparseMachine.familyEncoding
    (fun p : Input × RawAffineBranchMachine.Templates =>
      RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput p)) :=
  RawAffineBranchMachine.bodyExecutes.comp RationalAffineBodyMachine.executes

def branchesExecutes : Executes encoding RationalDisjunctionMachine.systemsEncoding branchSystems :=
  NegativeCertificateMachine.Lists.map encoding RawAffineBranchMachine.templatesEncoding
    RationalSparseMachine.familyEncoding
    ((Executes.ofComputes OriginalFamilyPackingMachine.family).comp RawAffineFamilyEnumeration.executes)
    (fun r t => RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput (r,t))) branchCell

def bodyExecutes : Executes encoding RationalSparseMachine.familyEncoding body := by
  let width := Executes.ofComputes OriginalFamilyPackingMachine.widthComputes
  let combined := (width.pair branchesExecutes).comp RationalDisjunctionMachine.executes
  let guard := width.comp RationalMatrixMachine.guardExecutes
  exact (guard.pair combined).comp
    (Executes.ofComputes (StructuralListMachine.consComputes RationalSparseMachine.encoding))

def prepare : Executes encoding RationalInputMachine.encoding request := by
  let wire := (Executes.ofComputes OriginalFamilyPackingMachine.widthComputes).pair
    ((Executes.ofComputes OriginalFamilyPackingMachine.rootsComputes).pair
      (bodyExecutes.pair OriginalFamilyPackingMachine.addressesExecutes))
  exact Executes.recode wire id (fun _ => rfl) (fun _ => rfl)

def machine := prepare.machine.compose OriginalSystemMachine.machine

def prepared_outputs (r : Input) : TM2OutputsInTime prepare.machine.computer
    (encoding.encode r) (some (RationalInputMachine.encoding.encode (request r)))
    (prepare.cost r) := prepare.outputs r

theorem preparation_primitive_bound (r : Input) :
    primitiveCost prepare.machine (prepare.outputs r).steps
      (some (initList prepare.machine.computer (encoding.encode r))) ≤
        prepare.cost r*prepare.machine.primitiveBudget := prepare.primitive_bound r
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineRecognitionMachine
