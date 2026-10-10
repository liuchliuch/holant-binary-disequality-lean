import Holant.Proofs.Recognition.RuntimeTensorRequest
import Holant.Proofs.Recognition.PromisedListMap

/-! Runtime label and zero/nonzero candidate enumeration. One zero branch is
followed by every literally generated metadata packet. These programmes read
arity/count from source rows; they do not specialize control to a chosen layout.
No candidate is asserted successful by this enumeration component. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorEnumeration
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open PhysicalFolds
open RuntimeTensorRequest (Context contextEncoding Candidate candidateEncoding)
open UniformTensorWitnessBranch (Metadata metadataEncoding)

abbrev FamilyInput := RuntimeTensorRequest.Flags × OriginalFamilyPackingMachine.Input
abbrev familyEncoding := pairEncoding RuntimeTensorRequest.flagsEncoding OriginalFamilyPackingMachine.encoding
abbrev indexEncoding := framedListEncoding encodingNatBool
abbrev candidatesEncoding := framedListEncoding candidateEncoding

def zeroCandidate : Candidate := (true,([],[],[]))
def candidates (n : ℕ) : List Candidate := zeroCandidate ::
  (RuntimeTensorCatalogue.catalogue n).map (fun m => (false,m))
def labels (r : FamilyInput) : List ℕ := List.range r.2.1.length

theorem mem_candidates (n : ℕ) (c : Candidate) :
    c∈candidates n ↔ c=zeroCandidate ∨ c.1=false ∧ c.2∈RuntimeTensorCatalogue.catalogue n := by
  rcases c with ⟨b,m⟩
  simp [candidates,Prod.mk.injEq,and_assoc,and_comm,eq_comm]

theorem candidate_domain (n : ℕ) (c : Candidate) (h : c∈candidates n) :
    c.1=true ∨ c.2∈RuntimeTensorCatalogue.catalogue n := by
  rcases (mem_candidates n c).mp h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr h.2

theorem zero_mem (n : ℕ) : zeroCandidate∈candidates n := List.mem_cons_self ..
theorem nonzero_mem (n : ℕ) (m : Metadata) (hm : m∈RuntimeTensorCatalogue.catalogue n) :
    (false,m)∈candidates n := (mem_candidates n _).mpr (Or.inr ⟨rfl,hm⟩)

def atLabel (p : FamilyInput × ℕ) : Context := (p.1.2,p.1.1,p.2)
def arity (c : Context) : ℕ := (c.1.1.getD c.2.2 (0,[])).1

theorem labels_source {s : ℕ} (a : Fin s → ℕ) (input : OriginalFamilyInput.Input a)
    (flags : RuntimeTensorRequest.Flags) :
    labels (flags,OriginalFamilyPackingSource.fromSource a input false)=List.range s := by
  simp only [labels,OriginalFamilyPackingSource.family_length]

noncomputable section
set_option backward.isDefEq.respectTransparency false

def candidatesExecutes : Executes encodingNatBool candidatesEncoding candidates := by
  let attach := WireLists.mapComputes metadataEncoding candidateEncoding (fun m : Metadata => (false,m))
    (pairComputes (constantComputes metadataEncoding encodingBoolBool false) (identityComputes metadataEncoding))
  let all := RuntimeTensorCatalogue.executes.comp (Executes.ofComputes attach)
  exact ((Executes.ofComputes (constantComputes encodingNatBool candidateEncoding zeroCandidate)).pair all).comp
    (Executes.ofComputes (StructuralListMachine.consComputes candidateEncoding))

def labelsExecutes : Executes familyEncoding indexEncoding labels :=
  (Executes.ofComputes (((Wiring.secondComputes RuntimeTensorRequest.flagsEncoding
    OriginalFamilyPackingMachine.encoding).andThen OriginalFamilyPackingMachine.family).andThen
      ((WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding).andThen UnaryBinary.computes))).comp
        RationalInputMachine.Programs.range

def atLabelComputes : Computes (pairEncoding familyEncoding encodingNatBool) contextEncoding atLabel := by
  let source := Wiring.firstComputes familyEncoding encodingNatBool
  let flags := source.andThen (Wiring.firstComputes RuntimeTensorRequest.flagsEncoding OriginalFamilyPackingMachine.encoding)
  let original := source.andThen (Wiring.secondComputes RuntimeTensorRequest.flagsEncoding OriginalFamilyPackingMachine.encoding)
  let label := Wiring.secondComputes familyEncoding encodingNatBool
  exact pairComputes original (pairComputes flags label)

def arityExecutes : Executes contextEncoding encodingNatBool arity :=
  (Executes.ofComputes (pairComputes (identityComputes contextEncoding)
    (constantComputes contextEncoding candidateEncoding zeroCandidate))).comp RuntimeTensorRequest.arityExecutes

def forContextExecutes : Executes contextEncoding candidatesEncoding (fun c => candidates (arity c)) :=
  arityExecutes.comp candidatesExecutes

/-- The erased index only restricts correctness; the programme is the already
constructed runtime controller, not one selected separately for each index. -/
def ofExecutes {D A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool} {f : A → B}
    (w : Executes ea eb f) (input : D → A) : Runs ea eb input (fun d => f (input d)) :=
  ⟨w.machine,fun d => w.cost (input d),fun d => w.outputs (input d)⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorEnumeration
