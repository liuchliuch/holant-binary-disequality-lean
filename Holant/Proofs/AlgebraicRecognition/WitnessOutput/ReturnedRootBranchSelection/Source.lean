import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Bounded
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.BranchConsumers.ComparisonBoundary


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open CommonFieldMachine (Executes)

namespace Source
abbrev zeroList := ReturnedRootBranchSelection.zeroList
abbrev zeroPolynomial := ReturnedRootBranchSelection.zeroPolynomial
abbrev first {B : Type} : (o : Output) → Valid o.root → Catalogue B → Option B :=
  ReturnedRootBranchSelection.first (B:=B)

theorem zero_iff (c : RootCode) (v : List ℚ) (hv : Valid c) (z : ℂ) (hz : c.Represents z) :
    zeroList c v hv=true ↔ BranchConsumers.decodeList z v=0 := zeroList_iff c v hv z hz

/-- The required reducible-relation boundary is accepted without deleting the
nonzero coordinate or adding minimality to the returned root metadata. -/
theorem splitRoot_zero :
    zeroList BranchConsumers.splitRoot [0,1]
      ⟨0,BranchConsumers.splitRoot_represents_zero⟩=true :=
  (zero_iff BranchConsumers.splitRoot [0,1] ⟨0,BranchConsumers.splitRoot_represents_zero⟩
    0 BranchConsumers.splitRoot_represents_zero).mpr BranchConsumers.reducible_relation_boundary.2.2

theorem selected_same_root {B : Type} (o : Output) (hv : Valid o.root) (cs : Catalogue B)
    (b : B) (hb : first o hv cs=some b) (z : ℂ) (hz : o.root.Represents z) :
    ∃ S, (b,S)∈cs ∧ ∀ p ∈ S, Evaluate.rowValue z o.variables p=0 := by
  obtain ⟨S,hS,hpass⟩ := first_sound o hv cs b hb
  exact ⟨S,hS,(passes_iff o hv z hz S).mp hpass⟩

theorem bounded_matches_first {B : Type} (o : Output) (hv : Valid o.root)
    (es : List Evidence) (cs : Catalogue B) (hk : (Bounded.select o es cs).1=true) :
    Bounded.packet o es cs=(o,(true,first o hv cs)) :=
  Prod.ext rfl (Prod.ext hk (Bounded.select_sound o hv es cs hk))
end Source

namespace Physical
noncomputable section
abbrev checker := ReturnedRootBranchSelection.executes
abbrev scan := Scan.executes
abbrev ListInput := RootCode × (List ℚ × List Evidence)
abbrev listInputEncoding := pairEncoding ComplexIsolation.CertificateMachine.rootEncoding
  (pairEncoding CommonFieldMachine.coordinatesEncoding Scan.evidenceListEncoding)
def listScan (x : ListInput) : Option Bool := Scan.first (x.1,Code.dense x.2.1) x.2.2
def listScanExecutes : Executes listInputEncoding Scan.resultEncoding listScan := by
  let c := Wiring.firstComputes ComplexIsolation.CertificateMachine.rootEncoding
    (pairEncoding CommonFieldMachine.coordinatesEncoding Scan.evidenceListEncoding)
  let tail := Wiring.secondComputes ComplexIsolation.CertificateMachine.rootEncoding
    (pairEncoding CommonFieldMachine.coordinatesEncoding Scan.evidenceListEncoding)
  let v := tail.andThen (Wiring.firstComputes CommonFieldMachine.coordinatesEncoding Scan.evidenceListEncoding)
  let es := tail.andThen (Wiring.secondComputes CommonFieldMachine.coordinatesEncoding Scan.evidenceListEncoding)
  let prepare := pairComputes (pairComputes c (v.andThen CodePrograms.denseComputes)) es
  exact (Executes.ofComputes prepare).comp Scan.executes
def listScan_outputs (x : ListInput) : TM2OutputsInTime listScanExecutes.machine.computer
    (listInputEncoding.encode x) (some (Scan.resultEncoding.encode (listScan x))) (listScanExecutes.cost x) :=
  listScanExecutes.outputs x
theorem listScan_sound (x : ListInput) (z : ℂ) (hz : x.1.Represents z)
    (b : Bool) (hb : listScan x=some b) : b=true ↔ BranchConsumers.decodeList z x.2.1=0 := by
  simpa only [Code.dense_correct] using (Scan.first_sound hz hb)

abbrev Input := Raw × (Output × List Evidence)
abbrev contextEncoding := Bounded.contextEncoding
abbrev inputEncoding := pairEncoding rawEncoding contextEncoding

def product (x : Input) : Output × (Bool × Option ProductCode) :=
  Bounded.packet x.2.1 x.2.2 (productCatalogue x.1)
def «local» (x : Input) : Output × (Bool × Option LocalCode) :=
  Bounded.packet x.2.1 x.2.2 (localCatalogue x.1)
def affine (x : Input) : Output × (Bool × Option AffineCode) :=
  Bounded.packet x.2.1 x.2.2 (affineCatalogue x.1)
abbrev productEncoding := pairEncoding outputEncoding
  (Bounded.resultEncoding RawProductFamilyEnumeration.candidateEncoding)
abbrev localEncoding := pairEncoding outputEncoding
  (Bounded.resultEncoding RawLocalAffineFamilyEnumeration.candidateEncoding)
abbrev affineEncoding := pairEncoding outputEncoding
  (Bounded.resultEncoding RawAffineBranchMachine.templatesEncoding)

def productExecutes : Executes inputEncoding productEncoding product :=
  ((Executes.ofComputes (Wiring.secondComputes rawEncoding contextEncoding)).pair
    ((Executes.ofComputes (Wiring.firstComputes rawEncoding contextEncoding)).comp productCatalogueExecutes)).comp
      (Bounded.packetExecutes RawProductFamilyEnumeration.candidateEncoding ([],[]))
def localExecutes : Executes inputEncoding localEncoding «local» :=
  ((Executes.ofComputes (Wiring.secondComputes rawEncoding contextEncoding)).pair
    ((Executes.ofComputes (Wiring.firstComputes rawEncoding contextEncoding)).comp localCatalogueExecutes)).comp
      (Bounded.packetExecutes RawLocalAffineFamilyEnumeration.candidateEncoding [])
def affineExecutes : Executes inputEncoding affineEncoding affine :=
  ((Executes.ofComputes (Wiring.secondComputes rawEncoding contextEncoding)).pair
    ((Executes.ofComputes (Wiring.firstComputes rawEncoding contextEncoding)).comp affineCatalogueExecutes)).comp
      (Bounded.packetExecutes RawAffineBranchMachine.templatesEncoding ([],(0,[],0,[],[])))

def product_outputs (x : Input) : TM2OutputsInTime productExecutes.machine.computer
    (inputEncoding.encode x) (some (productEncoding.encode (product x))) (productExecutes.cost x) :=
  productExecutes.outputs x
def local_outputs (x : Input) : TM2OutputsInTime localExecutes.machine.computer
    (inputEncoding.encode x) (some (localEncoding.encode («local» x))) (localExecutes.cost x) :=
  localExecutes.outputs x
def affine_outputs (x : Input) : TM2OutputsInTime affineExecutes.machine.computer
    (inputEncoding.encode x) (some (affineEncoding.encode (affine x))) (affineExecutes.cost x) :=
  affineExecutes.outputs x

theorem product_primitives (x : Input) : primitiveCost productExecutes.machine (product_outputs x).steps
    (some (initList productExecutes.machine.computer (inputEncoding.encode x))) ≤
      productExecutes.cost x*productExecutes.machine.primitiveBudget := productExecutes.primitive_bound x
theorem local_primitives (x : Input) : primitiveCost localExecutes.machine (local_outputs x).steps
    (some (initList localExecutes.machine.computer (inputEncoding.encode x))) ≤
      localExecutes.cost x*localExecutes.machine.primitiveBudget := localExecutes.primitive_bound x
theorem affine_primitives (x : Input) : primitiveCost affineExecutes.machine (affine_outputs x).steps
    (some (initList affineExecutes.machine.computer (inputEncoding.encode x))) ≤
      affineExecutes.cost x*affineExecutes.machine.primitiveBudget := affineExecutes.primitive_bound x

@[simp] theorem product_payload (x : Input) : (product x).1=x.2.1 := rfl
@[simp] theorem local_payload (x : Input) : («local» x).1=x.2.1 := rfl
@[simp] theorem affine_payload (x : Input) : (affine x).1=x.2.1 := rfl

theorem product_sound (x : Input) (hv : Valid x.2.1.root) (hk : (product x).2.1=true) :
    (product x).2.2=Source.first x.2.1 hv (productCatalogue x.1) := Bounded.select_sound _ hv _ _ hk
theorem local_sound (x : Input) (hv : Valid x.2.1.root) (hk : («local» x).2.1=true) :
    («local» x).2.2=Source.first x.2.1 hv (localCatalogue x.1) := Bounded.select_sound _ hv _ _ hk
theorem affine_sound (x : Input) (hv : Valid x.2.1.root) (hk : (affine x).2.1=true) :
    (affine x).2.2=Source.first x.2.1 hv (affineCatalogue x.1) := Bounded.select_sound _ hv _ _ hk
end
end Physical
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
