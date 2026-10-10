import Holant.Proofs.Algorithms.TransformRecognition.RawProductBranchMachine
import Mathlib.Data.List.Forall2


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawProductCandidateSource
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation.RootSearchDriver (mem_cross)
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm (Edge Skeleton)
open ProductVariableLayout (Slot slotArity)
variable {s : ℕ} (arity : Fin s → ℕ)

def generated (input : OriginalFamilyInput.Input arity) :=
  RawProductFamilyEnumeration.candidates (OriginalCatalogueSource.family arity input)
def slotCode (c : RawProductFamilyEnumeration.Candidate) : Slot s → RawProductFamilyEnumeration.Template
  | .inl i => c.1.getD i.val []
  | .inr _ => c.2

theorem choices_exact (input : OriginalFamilyInput.Input arity) :
    RawProductFamilyEnumeration.choices (OriginalCatalogueSource.family arity input) =
      List.ofFn (fun i => RawProductEnumeration.templates (arity i)) := by
  simp only [RawProductFamilyEnumeration.choices,OriginalCatalogueSource.family,
    OriginalFamilyPackingSource.fromSource,List.map_map,Function.comp_def,List.ofFn_eq_map]

theorem vertex_relation (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input) :
    List.Forall₂ (fun xs d => d ∈ xs)
      (List.ofFn (fun i => RawProductEnumeration.templates (arity i))) c.1 := by
  have h := (StructuralChoicesMachine.mem_product_iff _ _).mp (mem_cross.mp hc).1
  rwa [choices_exact] at h

theorem vertex_length (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input) : c.1.length=s := by
  have h := (vertex_relation arity input c hc).length_eq
  simpa only [List.length_ofFn] using h.symm

theorem slot_generated (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input) (j : Slot s) :
    slotCode c j ∈ RawProductEnumeration.templates (slotArity arity j) := by
  cases j with
  | inl i =>
    have h := vertex_relation arity input c hc
    have hi : i.val<c.1.length := by rw [vertex_length arity input c hc]; exact i.isLt
    have hl : i.val<(List.ofFn (fun i => RawProductEnumeration.templates (arity i))).length := by
      simpa only [List.length_ofFn] using i.isLt
    have hg := h.get hl hi
    simpa only [slotCode,slotArity,Sum.elim_inl,List.getD_eq_getElem c.1 [] hi,
      List.get_eq_getElem,List.getElem_ofFn] using hg
  | inr u => exact (mem_cross.mp hc).2

noncomputable def edgesAt (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input)
    (j : Slot s) : List (Edge (slotArity arity j)) :=
  Classical.choose (RawProductEnumeration.reify (slotCode c j) (slot_generated arity input c hc j))

theorem edgesAt_exact (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input) (j : Slot s) :
    slotCode c j = (edgesAt arity input c hc j).map RationalProductTemplateSource.edgeCode :=
  Classical.choose_spec (RawProductEnumeration.reify (slotCode c j) (slot_generated arity input c hc j))

noncomputable def normalized (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input) : ProductBranch.Branch arity :=
  fun j => (edgesAt arity input c hc j).toFinset

theorem sourceCode_slot (B : ProductBranch.Branch arity) (j : Slot s) :
    slotCode (RawProductFamilyEnumeration.sourceCode arity B) j =
      (B j).toList.map RationalProductTemplateSource.edgeCode := by
  cases j with
  | inl i =>
    exact Holant.LocalDrafts.EffectiveAlgebraic.PositiveCertificateMachine.getD_ofFn
      (fun i => (B (.inl i)).toList.map RationalProductTemplateSource.edgeCode) i []
  | inr u => rfl

theorem normalized_source (input : OriginalFamilyInput.Input arity)
    (B : ProductBranch.Branch arity)
    (hc : RawProductFamilyEnumeration.sourceCode arity B ∈ generated arity input) :
    normalized arity input (RawProductFamilyEnumeration.sourceCode arity B) hc = B := by
  funext j
  have h := edgesAt_exact arity input (RawProductFamilyEnumeration.sourceCode arity B) hc j
  rw [sourceCode_slot] at h
  have he := (List.map_injective_iff.mpr RawProductEnumeration.edgeCode_injective) h
  change (edgesAt arity input (RawProductFamilyEnumeration.sourceCode arity B) hc j).toFinset = B j
  rw [←he]
  ext e
  simp

theorem value_exact {v : ℕ} (input : OriginalFamilyInput.Input arity)
    (c : RawProductFamilyEnumeration.Candidate) (hc : c ∈ generated arity input)
    (j : Slot s) (address : Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Parameter
      (slotArity arity j) → Fin v) (x : Fin (slotArity arity j) → Bool) :
    RationalProductTemplateMachine.value
      (v,slotCode c j,(address none).val,
        List.ofFn (fun k => ((address (some (k,false))).val,(address (some (k,true))).val)),List.ofFn x) =
      RationalInputMachine.rowWire (SparseProductTemplate.entry RationalCompiler.data
        (OriginalProductSystem.edgeList (normalized arity input c hc j)) address x) := by
  rw [edgesAt_exact arity input c hc j]
  change RationalProductTemplateMachine.value
    (RationalProductTemplateSource.fromSource (edgesAt arity input c hc j) address x) = _
  rw [RationalProductTemplateSource.value_source,RawProductEnumeration.entry_normalized]
  rfl

end Holant.LocalDrafts.MainChain.TransformRecognition.RawProductCandidateSource
