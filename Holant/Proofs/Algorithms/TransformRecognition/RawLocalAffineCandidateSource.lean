import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineFamilyEnumeration
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineCandidateSource
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineAllocationMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineCandidateSource
set_option backward.isDefEq.respectTransparency false
open Holant.Tractable
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition

abbrev Choice := RawLocalAffineEnumeration.Choice
abbrev Candidate := RawLocalAffineEnumeration.Candidate

def atWord (n : ℕ) (c : Candidate) (a : Fin n → Bool) : Choice :=
  c.getD ((SparseTransform.allWords n).idxOf a) LocalAffineAllocationMachine.emptyChoice

theorem word_index_lt {n : ℕ} (a : Fin n → Bool) :
    (SparseTransform.allWords n).idxOf a < (SparseTransform.allWords n).length :=
  List.idxOf_lt_length_iff.mpr (SparseTransform.mem_allWords a)

theorem atWord_mem (n : ℕ) (c : Candidate) (hc : c ∈ RawLocalAffineEnumeration.candidates n)
    (a : Fin n → Bool) : atWord n c a ∈ c := by
  apply RawAffineEnumerationValidity.bounded_get_mem
  rw [RawLocalAffineEnumeration.generated_length n c hc,RationalTableMachine.words_eq,List.length_map]
  exact word_index_lt a

theorem atWord_regular (n : ℕ) (c : Candidate) (hc : c ∈ RawLocalAffineEnumeration.candidates n)
    (a : Fin n → Bool) : (atWord n c a).2.1=n ∧ EncodedTable.Regular (atWord n c a).2 :=
  RawLocalAffineEnumeration.generated_regular n c hc _ (atWord_mem n c hc a)

def normalized (n : ℕ) (c : Candidate) (hc : c ∈ RawLocalAffineEnumeration.candidates n) :
    LocalAffineNormalForm.Code n :=
  (Finset.univ.filter (fun a => (atWord n c a).1=true),
    fun a => RawAffineCandidateSource.normalizeAt n (atWord n c a).2 (atWord_regular n c hc a).1)

theorem normalized_mask (n : ℕ) (c : Candidate) (hc : c ∈ RawLocalAffineEnumeration.candidates n)
    (a : Fin n → Bool) : decide (a ∈ (normalized n c hc).1)=(atWord n c a).1 := by
  simp [normalized]

theorem normalized_coefficient {v : ℕ} (imaginary : Fin v) (n : ℕ)
    (c : Candidate) (hc : c ∈ RawLocalAffineEnumeration.candidates n) (a x : Fin n → Bool) :
    RationalAffineTemplateMachine.value (v,imaginary.val,(atWord n c a).2,List.ofFn x)=
      RationalInputMachine.rowWire
        (SymbolicPhaseCoefficients.affineCoefficient imaginary ((normalized n c hc).2 a) x) :=
  RawAffineCandidateSource.coefficient_at imaginary (atWord n c a).2
    (atWord_regular n c hc a).1 (atWord_regular n c hc a).2 x

theorem atWord_source {n : ℕ} (B : LocalAffineNormalForm.Code n) (a : Fin n → Bool) :
    atWord n (RawLocalAffineEnumeration.source B) a =
      (decide (a ∈ B.1),RationalAffineTemplateSource.sourceCode (B.2 a)) := by
  unfold atWord RawLocalAffineEnumeration.source
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using word_index_lt a),
    List.getElem_map,List.getElem_idxOf]

theorem reconstruct (n : ℕ) (c : Candidate) (hc : c ∈ RawLocalAffineEnumeration.candidates n) :
    (SparseTransform.allWords n).map (atWord n c)=c := by
  have hlen : c.length=(SparseTransform.allWords n).length := by
    simpa only [RationalTableMachine.words_eq,List.length_map] using
      RawLocalAffineEnumeration.generated_length n c hc
  apply List.ext_getElem
  · simp only [List.length_map,hlen]
  · intro i hi hj
    have hi' : i<(SparseTransform.allWords n).length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map,atWord,(SparseTransform.allWords_nodup n).idxOf_getElem i hi',
      List.getD_eq_getElem _ _ hj]

variable {s : ℕ} (arity : Fin s → ℕ)
def generated (input : OriginalFamilyInput.Input arity) :=
  RawLocalAffineFamilyEnumeration.candidates (OriginalCatalogueSource.family arity input)
def slotNumber : ProductVariableLayout.Slot s → ℕ := OriginalCatalogueSource.slotNumber

theorem choices_exact (input : OriginalFamilyInput.Input arity) :
    RawLocalAffineFamilyEnumeration.choices (OriginalCatalogueSource.family arity input) =
      (ProductVariableLayout.slots s).map (fun j =>
        RawLocalAffineEnumeration.candidates (ProductVariableLayout.slotArity arity j)) := by
  simp only [RawLocalAffineFamilyEnumeration.choices,OriginalCatalogueMachine.extended,
    OriginalCatalogueSource.family,OriginalFamilyPackingSource.fromSource,ProductVariableLayout.slots,
    List.map_append,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
    ProductVariableLayout.slotArity,Sum.elim_inl,Sum.elim_inr]

def slotCode (c : RawLocalAffineFamilyEnumeration.Candidate) (j : ProductVariableLayout.Slot s) : Candidate :=
  c.getD (OriginalCatalogueSource.slotNumber j) []

theorem slot_generated (input : OriginalFamilyInput.Input arity)
    (c : RawLocalAffineFamilyEnumeration.Candidate) (hc : c ∈ generated arity input)
    (j : ProductVariableLayout.Slot s) :
    slotCode c j ∈ RawLocalAffineEnumeration.candidates (ProductVariableLayout.slotArity arity j) := by
  have h := RawLocalAffineFamilyEnumeration.generated_relation _ c hc
  rw [choices_exact] at h
  have hj : OriginalCatalogueSource.slotNumber j < (ProductVariableLayout.slots s).length := by
    cases j with
    | inl i => simpa [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber] using Nat.lt_succ_of_lt i.isLt
    | inr u => simp [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber]
  have hcidx : OriginalCatalogueSource.slotNumber j < c.length := by
    rw [←h.length_eq,List.length_map]
    exact hj
  have hg := h.get (by simpa only [List.length_map] using hj) hcidx
  have hjget : (ProductVariableLayout.slots s)[OriginalCatalogueSource.slotNumber j]=j := by
    cases j with
    | inl i => simp [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber,List.getElem_append_left,i.isLt]
    | inr u => cases u; simp [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber]
  simpa only [slotCode,List.getD_eq_getElem _ [] hcidx,List.get_eq_getElem,List.getElem_map,hjget] using hg

def normalizedFamily (input : OriginalFamilyInput.Input arity)
    (c : RawLocalAffineFamilyEnumeration.Candidate) (hc : c ∈ generated arity input) :
    (j : ProductVariableLayout.Slot s) → LocalAffineNormalForm.Code (ProductVariableLayout.slotArity arity j) :=
  fun j => normalized _ (slotCode c j) (slot_generated arity input c hc j)

noncomputable def sourceFamily
    (B : (j : ProductVariableLayout.Slot s) → LocalAffineNormalForm.Code (ProductVariableLayout.slotArity arity j)) :
    RawLocalAffineFamilyEnumeration.Candidate :=
  (ProductVariableLayout.slots s).map (fun j => RawLocalAffineEnumeration.source (B j))

theorem sourceFamily_slot
    (B : (j : ProductVariableLayout.Slot s) → LocalAffineNormalForm.Code (ProductVariableLayout.slotArity arity j))
    (j : ProductVariableLayout.Slot s) :
    slotCode (sourceFamily arity B) j = RawLocalAffineEnumeration.source (B j) := by
  have hj : OriginalCatalogueSource.slotNumber j < (ProductVariableLayout.slots s).length := by
    cases j with
    | inl i => simpa [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber] using Nat.lt_succ_of_lt i.isLt
    | inr u => simp [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber]
  unfold slotCode sourceFamily
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hj),List.getElem_map]
  have he : (ProductVariableLayout.slots s)[OriginalCatalogueSource.slotNumber j]=j := by
    cases j with
    | inl i => simp [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber,List.getElem_append_left,i.isLt]
    | inr u => cases u; simp [ProductVariableLayout.slots,OriginalCatalogueSource.slotNumber]
  exact congrArg (fun k => RawLocalAffineEnumeration.source (B k)) he

theorem sourceFamily_mem (input : OriginalFamilyInput.Input arity)
    (B : (j : ProductVariableLayout.Slot s) → LocalAffineNormalForm.Code (ProductVariableLayout.slotArity arity j)) :
    sourceFamily arity B ∈ generated arity input := by
  apply (StructuralChoicesMachine.mem_product_iff _ _).mpr
  rw [choices_exact]
  unfold sourceFamily
  have h : ∀ js : List (ProductVariableLayout.Slot s),
      List.Forall₂ (fun cs c => c ∈ cs)
        (js.map (fun j => RawLocalAffineEnumeration.candidates (ProductVariableLayout.slotArity arity j)))
        (js.map (fun j => RawLocalAffineEnumeration.source (B j))) := by
    intro js
    induction js with
    | nil => exact .nil
    | cons j js ih => exact .cons (RawLocalAffineEnumeration.source_mem (B j)) ih
  exact h _
end Holant.LocalDrafts.MainChain.TransformRecognition.RawLocalAffineCandidateSource
