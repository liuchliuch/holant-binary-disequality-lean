import Holant.Proofs.Recognition.RuntimeTensorBasis
import Holant.Proofs.Recognition.RuntimeTensorRows
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAllocatedPackingMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAddressTablesMachine
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Original

/-!
# Runtime original-root tensor request compiler

The whole arity layout, selected label and candidate are runtime data. The
programme generates the equality edge and standard I/positive-sqrt2 descriptors,
allocates one inverse-pivot slot, constructs actual original coefficient
addresses, fixes identity/K/KX, and emits the sparse system. Invalid nonzero
metadata is replaced internally by an unsatisfiable constant-one equation.

This file constructs the uniform arithmetic/request programme, including its
same-programme costs. Original-root search termination and exact tensor-class
recognition require the subsequent promised-domain source theorem; neither is
assumed or asserted here for malformed arbitrary root inputs.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorRequest
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open UniformTensorWitnessBranch (Metadata metadataEncoding)

abbrev Flags := Bool × Bool
abbrev flagsEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev Context := OriginalFamilyPackingMachine.Input × (Flags × ℕ)
abbrev contextTailEncoding := pairEncoding flagsEncoding encodingNatBool
abbrev contextEncoding := pairEncoding OriginalFamilyPackingMachine.encoding contextTailEncoding
abbrev Candidate := Bool × Metadata
abbrev candidateEncoding := pairEncoding encodingBoolBool metadataEncoding
abbrev Input := Context × Candidate
abbrev encoding := pairEncoding contextEncoding candidateEncoding

/-- The edge selector is generated internally, not inherited from a caller. -/
def source (r : Input) : OriginalFamilyPackingMachine.Input := (r.1.1.1,false)
def allocated (r : Input) : OriginalAllocatedPackingMachine.Input := (source r,1)
def width (r : Input) : ℕ := OriginalAllocatedPackingMachine.width (allocated r)
def native (r : Input) : Bool := r.1.2.1.1
def opposite (r : Input) : Bool := r.1.2.1.2
def label (r : Input) : ℕ := r.1.2.2
def zeroBranch (r : Input) : Bool := r.2.1
def candidate (r : Input) : Metadata := r.2.2
def arity (r : Input) : ℕ := ((source r).1.getD (label r) (0,[])).1
def imaginary (r : Input) : ℕ := 6+(OriginalFamilyPackingMachine.original (source r)).length

def basisInput (r : Input) : RuntimeTensorBasis.Input :=
  ((native r,opposite r),(width r,imaginary r,imaginary r+1))
def tableInput (r : Input) : OriginalAddressTablesMachine.Input := ((source r).1,1,label r)
def rowInput (r : Input) : RuntimeTensorRows.Input :=
  (width r,arity r,candidate r,OriginalAddressTablesMachine.table (tableInput r))
def candidateValid (r : Input) : Bool := RuntimeTensorValidation.valid (native r,arity r,candidate r)

def extraRows (r : Input) : List RationalSparseMachine.Poly :=
  if zeroBranch r then RuntimeTensorRows.zeroRows (rowInput r)
  else if candidateValid r then RuntimeTensorRows.rows (native r) (rowInput r)
  else [RationalSparseMachine.one (width r)]
def body (r : Input) : RationalInputMachine.Body := RuntimeTensorBasis.rows (basisInput r) ++ extraRows r

def request (r : Input) : RationalInputMachine.Input where
  «variables» := width r
  original := OriginalFamilyPackingMachine.roots (source r)
  body := body r
  addresses := OriginalAllocatedPackingMachine.addresses (allocated r)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def contextComputes := Wiring.firstComputes contextEncoding candidateEncoding
def selectionComputes := Wiring.secondComputes contextEncoding candidateEncoding
def rawComputes := contextComputes.andThen (Wiring.firstComputes OriginalFamilyPackingMachine.encoding contextTailEncoding)
def sourceComputes : Computes encoding OriginalFamilyPackingMachine.encoding source :=
  pairComputes (rawComputes.andThen OriginalFamilyPackingMachine.family)
    (constantComputes encoding encodingBoolBool false)
def allocatedComputes : Computes encoding OriginalAllocatedPackingMachine.encoding allocated :=
  pairComputes sourceComputes (constantComputes encoding encodingNatBool 1)
def widthComputes : Computes encoding encodingNatBool width :=
  allocatedComputes.andThen OriginalAllocatedPackingMachine.widthComputes

def tailComputes := contextComputes.andThen (Wiring.secondComputes OriginalFamilyPackingMachine.encoding contextTailEncoding)
def flagsComputes := tailComputes.andThen (Wiring.firstComputes flagsEncoding encodingNatBool)
def nativeComputes : Computes encoding encodingBoolBool native :=
  flagsComputes.andThen (Wiring.firstComputes encodingBoolBool encodingBoolBool)
def oppositeComputes : Computes encoding encodingBoolBool opposite :=
  flagsComputes.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)
def labelComputes : Computes encoding encodingNatBool label := tailComputes.andThen (Wiring.secondComputes flagsEncoding encodingNatBool)
def zeroComputes : Computes encoding encodingBoolBool zeroBranch :=
  selectionComputes.andThen (Wiring.firstComputes encodingBoolBool metadataEncoding)
def candidateComputes : Computes encoding metadataEncoding candidate :=
  selectionComputes.andThen (Wiring.secondComputes encodingBoolBool metadataEncoding)
def familyComputes := sourceComputes.andThen OriginalFamilyPackingMachine.family

def arityExecutes : Executes encoding encodingNatBool arity :=
  ((Executes.ofComputes (pairComputes familyComputes labelComputes)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))).comp
      (Executes.ofComputes (Wiring.firstComputes encodingNatBool CommonFieldMachine.rootsEncoding))

def imaginaryComputes : Computes encoding encodingNatBool imaginary :=
  (pairComputes (constantComputes encoding encodingNatBool 6)
    (sourceComputes.andThen OriginalFamilyPackingMachine.originalsCount)).andThen RationalInputMachine.Programs.add

def basisComputes : Computes encoding RuntimeTensorBasis.encoding basisInput :=
  pairComputes (pairComputes nativeComputes oppositeComputes)
    (pairComputes widthComputes (pairComputes imaginaryComputes
      (imaginaryComputes.andThen RationalInputMachine.Programs.successor)))

def tableComputes : Computes encoding OriginalAddressTablesMachine.encoding tableInput :=
  pairComputes familyComputes (pairComputes (constantComputes encoding encodingNatBool 1) labelComputes)

def rowExecutes : Executes encoding RuntimeTensorRows.encoding rowInput :=
  (Executes.ofComputes widthComputes).pair (arityExecutes.pair
    ((Executes.ofComputes candidateComputes).pair
      ((Executes.ofComputes tableComputes).comp OriginalAddressTablesMachine.executes)))

def validExecutes : Executes encoding encodingBoolBool candidateValid :=
  ((Executes.ofComputes nativeComputes).pair (arityExecutes.pair (Executes.ofComputes candidateComputes))).comp
    RuntimeTensorValidation.executes

def extraExecutes : Executes encoding RationalSparseMachine.familyEncoding extraRows := by
  let zero := rowExecutes.comp RuntimeTensorRows.zeroRowsExecutes
  let rows := ((Executes.ofComputes nativeComputes).pair rowExecutes).comp RuntimeTensorRows.rowsExecutes
  let reject := ((Executes.ofComputes widthComputes).comp RationalSparseMachine.oneExecutes).comp
    (Executes.ofComputes (NegativeCertificateMachine.Lists.singleton RationalSparseMachine.encoding))
  exact RuntimeTensorRows.choose encoding RationalSparseMachine.familyEncoding (Executes.ofComputes zeroComputes)
    zero (RuntimeTensorRows.choose encoding RationalSparseMachine.familyEncoding validExecutes rows reject)

def bodyExecutes : Executes encoding RationalInputMachine.bodyEncoding body :=
  (((Executes.ofComputes basisComputes).comp RuntimeTensorBasis.executes).pair extraExecutes).comp
    (Executes.ofComputes (WireLists.append RationalSparseMachine.encoding))

/-- One request compiler for all runtime dimensions and original coefficient rows. -/
def executes : Executes encoding RationalInputMachine.encoding request := by
  let raw := (Executes.ofComputes widthComputes).pair
    ((Executes.ofComputes (sourceComputes.andThen OriginalFamilyPackingMachine.rootsComputes)).pair
      (bodyExecutes.pair ((Executes.ofComputes allocatedComputes).comp OriginalAllocatedPackingMachine.addressesExecutes)))
  exact Executes.recode raw id (fun _ => rfl) (fun _ => rfl)

/-- Only composition syntax: promised-valid termination is a separate theorem. -/
def machine : BinaryCompose.Machine := executes.machine.compose WitnessOutput.originalMachine

def source_outputs (r : Input) : TM2OutputsInTime executes.machine.computer (encoding.encode r)
    (some (RationalInputMachine.encoding.encode (request r))) (executes.cost r) := executes.outputs r

theorem primitive_bound (r : Input) : primitiveCost executes.machine (executes.outputs r).steps
    (some (initList executes.machine.computer (encoding.encode r)))≤executes.cost r*executes.machine.primitiveBudget :=
  executes.primitive_bound r

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorRequest
