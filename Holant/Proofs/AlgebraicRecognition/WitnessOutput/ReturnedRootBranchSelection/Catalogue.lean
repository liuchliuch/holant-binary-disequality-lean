import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Evaluation
import Holant.Proofs.Algorithms.TransformRecognition.RawProductRecognitionMachine
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineRecognitionMachine
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRecognitionMachine


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Raw := OriginalFamilyPackingMachine.Input
abbrev rawEncoding := OriginalFamilyPackingMachine.encoding
abbrev ProductCode := RawProductFamilyEnumeration.Candidate
abbrev LocalCode := RawLocalAffineFamilyEnumeration.Candidate
abbrev AffineCode := RawAffineBranchMachine.Templates
abbrev Entry (B : Type) := B × Evaluate.Body
abbrev Catalogue (B : Type) := List (Entry B)

def productCatalogue (r : Raw) : Catalogue ProductCode :=
  (RawProductFamilyEnumeration.candidates r.1).map
    (fun b => (b,RawProductBranchMachine.body (r,b)))
def localCatalogue (r : Raw) : Catalogue LocalCode :=
  (RawLocalAffineFamilyEnumeration.candidates r.1).map
    (fun b => (b,RawLocalAffineBranchMachine.body (r,b)))
def affineCatalogue (r : Raw) : Catalogue AffineCode :=
  (RawAffineFamilyEnumeration.candidates r.1).map
    (fun b => (b,RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput (r,b))))

@[simp] theorem productCatalogue_codes (r : Raw) :
    (productCatalogue r).map Prod.fst=RawProductFamilyEnumeration.candidates r.1 := by
  simp [productCatalogue,List.map_map,Function.comp_def]
@[simp] theorem productCatalogue_rows (r : Raw) :
    (productCatalogue r).map Prod.snd=RawProductRecognitionMachine.systems r := by
  simp [productCatalogue,RawProductRecognitionMachine.systems,List.map_map,Function.comp_def]
@[simp] theorem localCatalogue_codes (r : Raw) :
    (localCatalogue r).map Prod.fst=RawLocalAffineFamilyEnumeration.candidates r.1 := by
  simp [localCatalogue,List.map_map,Function.comp_def]
@[simp] theorem localCatalogue_rows (r : Raw) :
    (localCatalogue r).map Prod.snd=RawLocalAffineRecognitionMachine.systems r := by
  simp [localCatalogue,RawLocalAffineRecognitionMachine.systems,List.map_map,Function.comp_def]
@[simp] theorem affineCatalogue_codes (r : Raw) :
    (affineCatalogue r).map Prod.fst=RawAffineFamilyEnumeration.candidates r.1 := by
  simp [affineCatalogue,List.map_map,Function.comp_def]
@[simp] theorem affineCatalogue_rows (r : Raw) :
    (affineCatalogue r).map Prod.snd=RawAffineRecognitionMachine.branchSystems r := by
  simp [affineCatalogue,RawAffineRecognitionMachine.branchSystems,List.map_map,Function.comp_def]

def passes (o : Output) (hv : Valid o.root) (S : Evaluate.Body) : Bool :=
  S.all (fun p => zeroPolynomial o.root (Evaluate.row o.variables p) hv)

theorem passes_iff (o : Output) (hv : Valid o.root) (z : ℂ) (hz : o.root.Represents z)
    (S : Evaluate.Body) : passes o hv S=true ↔ ∀ p ∈ S, Evaluate.rowValue z o.variables p=0 := by
  simp only [passes,List.all_eq_true]
  constructor
  · intro h p hp
    have hzero := (zeroPolynomial_iff o.root (Evaluate.row o.variables p) hv z hz).mp (h p hp)
    simpa only [Evaluate.row_correct] using hzero
  · intro h p hp
    apply (zeroPolynomial_iff o.root (Evaluate.row o.variables p) hv z hz).mpr
    simpa only [Evaluate.row_correct] using h p hp

def first {B : Type} (o : Output) (hv : Valid o.root) : Catalogue B → Option B
  | [] => none
  | (b,S)::rest => if passes o hv S then some b else first o hv rest

theorem first_sound {B : Type} (o : Output) (hv : Valid o.root)
    (cs : Catalogue B) (b : B) (hb : first o hv cs=some b) :
    ∃ S, (b,S)∈cs ∧ passes o hv S=true := by
  induction cs with
  | nil => simp [first] at hb
  | cons e es ih =>
    rcases e with ⟨c,S⟩
    cases hs : passes o hv S with
    | true =>
      have hc : c=b := by simpa [first,hs] using hb
      subst c
      exact ⟨S,List.mem_cons_self,hs⟩
    | false =>
      obtain ⟨T,hT,hp⟩ := ih (by simpa [first,hs] using hb)
      exact ⟨T,List.mem_cons_of_mem _ hT,hp⟩

theorem first_none_iff {B : Type} (o : Output) (hv : Valid o.root) (cs : Catalogue B) :
    first o hv cs=none ↔ ∀ e ∈ cs, passes o hv e.2=false := by
  induction cs with
  | nil => simp [first]
  | cons e es ih =>
    rcases e with ⟨b,S⟩
    cases hs : passes o hv S <;> simp [first,hs,ih]

/-- Explicit first-match order: each literal earlier entry is rejected before
the selected original branch code is returned. -/
theorem first_prefix {B : Type} (o : Output) (hv : Valid o.root)
    (pre post : Catalogue B) (b : B) (S : Evaluate.Body)
    (hpre : ∀ e ∈ pre, passes o hv e.2=false) (hS : passes o hv S=true) :
    first o hv (pre++(b,S)::post)=some b := by
  induction pre with
  | nil => simp [first,hS]
  | cons e es ih =>
    rcases e with ⟨c,T⟩
    have hT := hpre (c,T) List.mem_cons_self
    have hrest : ∀ e ∈ es, passes o hv e.2=false :=
      fun e he => hpre e (List.mem_cons_of_mem _ he)
    simpa [first,hT] using ih hrest

theorem first_complete {B : Type} (o : Output) (hv : Valid o.root) (cs : Catalogue B)
    (h : ∃ e ∈ cs, passes o hv e.2=true) : ∃ b, first o hv cs=some b := by
  cases hf : first o hv cs with
  | some b => exact ⟨b,rfl⟩
  | none =>
    obtain ⟨e,he,hp⟩ := h
    have hn := (first_none_iff o hv cs).mp hf e he
    rw [hp] at hn
    contradiction

def productSelection (r : Raw) (o : Output) (hv : Valid o.root) : Output × Option ProductCode :=
  (o,first o hv (productCatalogue r))
def localSelection (r : Raw) (o : Output) (hv : Valid o.root) : Output × Option LocalCode :=
  (o,first o hv (localCatalogue r))
def affineSelection (r : Raw) (o : Output) (hv : Valid o.root) : Output × Option AffineCode :=
  (o,first o hv (affineCatalogue r))
@[simp] theorem productSelection_payload (r : Raw) (o : Output) (hv : Valid o.root) :
    (productSelection r o hv).1=o := rfl
@[simp] theorem localSelection_payload (r : Raw) (o : Output) (hv : Valid o.root) :
    (localSelection r o hv).1=o := rfl
@[simp] theorem affineSelection_payload (r : Raw) (o : Output) (hv : Valid o.root) :
    (affineSelection r o hv).1=o := rfl

noncomputable section
abbrev entryEncoding {B : Type} (eb : Encoding B Bool) := pairEncoding eb RationalInputMachine.bodyEncoding
abbrev catalogueEncoding {B : Type} (eb : Encoding B Bool) := framedListEncoding (entryEncoding eb)

def productCatalogueExecutes : Executes rawEncoding
    (catalogueEncoding RawProductFamilyEnumeration.candidateEncoding) productCatalogue := by
  let candidates := (Executes.ofComputes OriginalFamilyPackingMachine.family).comp RawProductFamilyEnumeration.executes
  let cell := (Executes.ofComputes (Wiring.secondComputes rawEncoding RawProductFamilyEnumeration.candidateEncoding)).pair
    RawProductBranchMachine.bodyExecutes
  exact NegativeCertificateMachine.Lists.map rawEncoding RawProductFamilyEnumeration.candidateEncoding
    (entryEncoding RawProductFamilyEnumeration.candidateEncoding) candidates
    (fun r b => (b,RawProductBranchMachine.body (r,b))) cell

def localCatalogueExecutes : Executes rawEncoding
    (catalogueEncoding RawLocalAffineFamilyEnumeration.candidateEncoding) localCatalogue := by
  let candidates := (Executes.ofComputes OriginalFamilyPackingMachine.family).comp RawLocalAffineFamilyEnumeration.executes
  let cell := (Executes.ofComputes (Wiring.secondComputes rawEncoding RawLocalAffineFamilyEnumeration.candidateEncoding)).pair
    RawLocalAffineBranchMachine.bodyExecutes
  exact NegativeCertificateMachine.Lists.map rawEncoding RawLocalAffineFamilyEnumeration.candidateEncoding
    (entryEncoding RawLocalAffineFamilyEnumeration.candidateEncoding) candidates
    (fun r b => (b,RawLocalAffineBranchMachine.body (r,b))) cell

def affineCatalogueExecutes : Executes rawEncoding
    (catalogueEncoding RawAffineBranchMachine.templatesEncoding) affineCatalogue := by
  let candidates := (Executes.ofComputes OriginalFamilyPackingMachine.family).comp RawAffineFamilyEnumeration.executes
  let cell := (Executes.ofComputes (Wiring.secondComputes rawEncoding RawAffineBranchMachine.templatesEncoding)).pair
    RawAffineRecognitionMachine.branchCell
  exact NegativeCertificateMachine.Lists.map rawEncoding RawAffineBranchMachine.templatesEncoding
    (entryEncoding RawAffineBranchMachine.templatesEncoding) candidates
    (fun r b => (b,RationalAffineBodyMachine.body (RawAffineBranchMachine.bodyInput (r,b)))) cell
end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
