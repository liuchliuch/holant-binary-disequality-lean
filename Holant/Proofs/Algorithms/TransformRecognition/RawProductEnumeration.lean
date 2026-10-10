import Holant.Proofs.Algorithms.TransformRecognition.RationalProductTemplateSource
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineEnumerationValidity
import Holant.Proofs.Algorithms.TransformRecognition.OriginalProductSystem


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawProductEnumeration
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm (Skeleton Edge)
open CommonFieldMachine (Executes)
open RootSearchDriver (cross mem_cross)

abbrev RawEdge := RationalProductTemplateMachine.Edge
abbrev edgeEncoding := RationalProductTemplateMachine.edgeEncoding
abbrev edgesEncoding := RationalProductTemplateMachine.edgesEncoding
abbrev outputEncoding := framedListEncoding edgesEncoding

def edges (n : ℕ) : List RawEdge := cross (cross (List.range n) (List.range n)) [false,true]
def templates (n : ℕ) : List (List RawEdge) := StructuredCatalogue.lists (edges n) (edges n).length

theorem edge_bound {n : ℕ} (e : RawEdge) (he : e ∈ edges n) : e.1.1<n ∧ e.1.2<n := by
  have h := (mem_cross.mp (mem_cross.mp he).1)
  exact ⟨List.mem_range.mp h.1,List.mem_range.mp h.2⟩

theorem edge_mem {n : ℕ} (e : Edge n) : RationalProductTemplateSource.edgeCode e ∈ edges n := by
  exact mem_cross.mpr ⟨mem_cross.mpr ⟨List.mem_range.mpr e.1.1.isLt,List.mem_range.mpr e.1.2.isLt⟩,
    by cases e.2 <;> simp⟩

theorem edgeCode_injective {n : ℕ} : Function.Injective (RationalProductTemplateSource.edgeCode (n:=n)) := by
  rintro ⟨⟨i,j⟩,b⟩ ⟨⟨k,l⟩,c⟩ h
  have hi : i=k := Fin.ext (congrArg (fun e : RawEdge => e.1.1) h)
  have hj : j=l := Fin.ext (congrArg (fun e : RawEdge => e.1.2) h)
  have hb : b=c := congrArg Prod.snd h
  subst k; subst l; subst c
  rfl

theorem source_mem {n : ℕ} (es : List (Edge n)) (hn : es.Nodup) :
    es.map RationalProductTemplateSource.edgeCode ∈ templates n := by
  have hs : es.map RationalProductTemplateSource.edgeCode ⊆ edges n := by
    intro e he
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
    exact edge_mem e
  exact RawAffineEnumeration.mem_lists _ _ _ ((hn.map edgeCode_injective).length_le_of_subset hs) hs

theorem skeleton_mem {n : ℕ} (S : Skeleton n) :
    S.toList.map RationalProductTemplateSource.edgeCode ∈ templates n :=
  source_mem S.toList S.nodup_toList

theorem reify {n : ℕ} (raw : List RawEdge) (hr : raw ∈ templates n) :
    ∃ es : List (Edge n), raw=es.map RationalProductTemplateSource.edgeCode := by
  have hall := (RawAffineEnumerationValidity.lists_spec (edges n) raw (edges n).length hr).2
  let es := raw.attach.map (fun e =>
    (((⟨e.val.1.1,(edge_bound e.val (hall e.val e.property)).1⟩,
      ⟨e.val.1.2,(edge_bound e.val (hall e.val e.property)).2⟩),e.val.2) : Edge n))
  refine ⟨es,?_⟩
  simp only [es,List.map_map,Function.comp_def,RationalProductTemplateSource.edgeCode]
  change raw = raw.attach.map Subtype.val
  simpa only [id_eq,List.map_id_fun] using (List.attach_map_val (l := raw) (f := id)).symm

/-- Duplicate constraints and enumeration order do not change the emitted
polynomial. The canonical list is obtained from the actual generated edges,
not supplied as a successful Product witness. -/
theorem entry_normalized {n v : ℕ} (es : List (Edge n))
    (address : Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Parameter n → Fin v)
    (x : Fin n → Bool) :
    SparseProductTemplate.entry RationalCompiler.data es address x =
      SparseProductTemplate.entry RationalCompiler.data
        (OriginalProductSystem.edgeList es.toFinset) address x := by
  have he : SparseProductTemplate.holdsCheck es x =
      SparseProductTemplate.holdsCheck (OriginalProductSystem.edgeList es.toFinset) x := by
    apply Bool.eq_iff_iff.mpr
    rw [SparseProductTemplate.holdsCheck_iff,SparseProductTemplate.holdsCheck_iff,
      OriginalProductSystem.edgeList_exact]
  simp only [SparseProductTemplate.entry,he]

noncomputable section

def edgesExecutes : Executes encodingNatBool edgesEncoding edges := by
  let range := RationalInputMachine.Programs.range
  let pairs := (range.pair range).comp (Executes.ofComputes
    (RootSearchDriver.crossComputes encodingNatBool encodingNatBool))
  exact (pairs.pair (Executes.ofComputes (constantComputes encodingNatBool
    (framedListEncoding encodingBoolBool) [false,true]))).comp
      (Executes.ofComputes (RootSearchDriver.crossComputes RationalProductTemplateMachine.portsEncoding encodingBoolBool))

def executes : Executes encodingNatBool outputEncoding templates := by
  let count := edgesExecutes.comp (Executes.ofComputes
    ((WireLists.lengthComputes edgeEncoding).andThen UnaryBinary.computes))
  exact (edgesExecutes.pair count).comp (StructuralListMachine.boundedExecutes edgeEncoding)

def outputs (n : ℕ) : TM2OutputsInTime executes.machine.computer
    (encodingNatBool.encode n) (some (outputEncoding.encode (templates n))) (executes.cost n) := executes.outputs n
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawProductEnumeration
