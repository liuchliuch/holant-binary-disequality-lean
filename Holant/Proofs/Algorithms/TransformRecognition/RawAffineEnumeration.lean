import Holant.Proofs.Algorithms.TransformRecognition.RationalAffineTemplateSource
import Holant.Proofs.Algorithms.TransformRecognition.RationalTableMachine
import Holant.Proofs.Algorithms.TransformRecognition.StructuralListMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineEnumeration
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open RootSearchDriver (cross mem_cross)

def rows (n : ℕ) : List EncodedTable.Row := cross [false,true] (RationalTableMachine.words n)
def supports (n : ℕ) : List (List EncodedTable.Row) := StructuredCatalogue.lists (rows n) (rows n).length
def linears (n : ℕ) : List (List (ZMod 4)) := StructuralListMachine.exactLength [0,1,2,3] n
def mixedRows (n : ℕ) : List (List (ZMod 4)) := StructuralListMachine.exactLength [0,2] n
def matrices (n : ℕ) : List (List (List (ZMod 4))) := StructuralListMachine.exactLength (mixedRows n) n
def phases (n : ℕ) : List EncodedTable.Phase := cross [0,1,2,3] (cross (linears n) (matrices n))
def templates (n : ℕ) : List EncodedTable.Data := (cross (supports n) (phases n)).map (fun p => (n,p))

def rowCode {n : ℕ} (e : AffineNormalForm.Equation n) : EncodedTable.Row :=
  (decide (e.2=1),List.ofFn (fun j => decide (e.1 j=1)))

theorem rowCode_injective {n : ℕ} : Function.Injective (rowCode (n:=n)) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hb := congrArg (fun r : EncodedTable.Row => FiniteCore.bit2 r.1) h
  simp only [rowCode,EncodedTable.bit2_residue] at hb
  have ha := List.ofFn_injective (congrArg Prod.snd h)
  apply Prod.ext
  · funext i
    have hi := congrArg FiniteCore.bit2 (congrFun ha i)
    simpa only [EncodedTable.bit2_residue] using hi
  · exact hb

theorem mem_words {n : ℕ} (x : Fin n → Bool) : List.ofFn x ∈ RationalTableMachine.words n := by
  rw [RationalTableMachine.words_eq]
  exact List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩

theorem row_mem {n : ℕ} (e : AffineNormalForm.Equation n) : rowCode e ∈ rows n := by
  apply mem_cross.mpr
  exact ⟨by cases decide (e.2=1) <;> simp,mem_words _⟩

theorem mem_lists {A : Type} (alphabet xs : List A) (h : ℕ)
    (hlen : xs.length ≤ h) (hmem : ∀ a ∈ xs, a ∈ alphabet) :
    xs ∈ StructuredCatalogue.lists alphabet h := by
  refine List.mem_flatMap.mpr ⟨xs.length,List.mem_range.mpr (by omega),?_⟩
  exact List.mem_map.mpr ⟨xs.get,FiniteBranchEnumeration.mem_vectors _ _
    (fun i => hmem _ (List.get_mem xs i)),List.ofFn_get xs⟩

theorem support_mem {n : ℕ} (C : AffineNormalForm.Code n) :
    C.1.toList.map rowCode ∈ supports n := by
  have hnodup := C.1.nodup_toList.map rowCode_injective
  have hsub : C.1.toList.map rowCode ⊆ rows n := by
    intro e he
    obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
    exact row_mem e
  exact mem_lists _ _ _ (hnodup.length_le_of_subset hsub) hsub

theorem exact_mem {A : Type} (alphabet : List A) {n : ℕ} (f : Fin n → A)
    (h : ∀ i, f i ∈ alphabet) : List.ofFn f ∈ StructuralListMachine.exactLength alphabet n :=
  List.mem_map.mpr ⟨f,FiniteBranchEnumeration.mem_vectors _ _ h,rfl⟩

theorem phase_mem {n : ℕ} (C : AffineNormalForm.Code n) :
    (RationalAffineTemplateSource.sourceCode C).2.2 ∈ phases n := by
  apply mem_cross.mpr
  refine ⟨FiniteBranchEnumeration.mem_residues4 C.2.1,mem_cross.mpr ⟨?_,?_⟩⟩
  · exact exact_mem _ _ (fun i => FiniteBranchEnumeration.mem_residues4 _)
  · apply exact_mem
    intro i
    apply exact_mem
    intro j
    cases C.2.2.2 i j <;> simp

theorem source_mem {n : ℕ} (C : AffineNormalForm.Code n) :
    RationalAffineTemplateSource.sourceCode C ∈ templates n := by
  apply List.mem_map.mpr
  exact ⟨(RationalAffineTemplateSource.sourceCode C).2,
    mem_cross.mpr ⟨support_mem C,phase_mem C⟩,rfl⟩

noncomputable section
abbrev supportListEncoding := framedListEncoding EncodedTable.rowsEncoding
abbrev vectorListEncoding := framedListEncoding EncodedTable.vectorEncoding
abbrev matrixListEncoding := framedListEncoding EncodedTable.matrixEncoding
abbrev phaseListEncoding := framedListEncoding EncodedTable.phaseEncoding
abbrev outputEncoding := framedListEncoding EncodedTable.encoding

def rowsExecutes : Executes encodingNatBool EncodedTable.rowsEncoding rows :=
  ((Executes.ofComputes (constantComputes encodingNatBool
    (framedListEncoding encodingBoolBool) [false,true])).pair RationalTableMachine.wordsExecutes).comp
      (Executes.ofComputes (RootSearchDriver.crossComputes encodingBoolBool EncodedTable.bitsEncoding))

def supportsExecutes : Executes encodingNatBool supportListEncoding supports := by
  let count := rowsExecutes.comp (Executes.ofComputes
    ((WireLists.lengthComputes EncodedTable.rowEncoding).andThen UnaryBinary.computes))
  exact (rowsExecutes.pair count).comp (StructuralListMachine.boundedExecutes EncodedTable.rowEncoding)

def vectorsExecutes (alphabet : List (ZMod 4)) :
    Executes encodingNatBool vectorListEncoding (fun n => StructuralListMachine.exactLength alphabet n) :=
  (Executes.ofComputes (pairComputes (identityComputes encodingNatBool)
    (constantComputes encodingNatBool EncodedTable.vectorEncoding alphabet))).comp
      (StructuralListMachine.exactExecutes ResidueCells.encoding4)

def matricesExecutes : Executes encodingNatBool matrixListEncoding matrices :=
  ((Executes.ofComputes (identityComputes encodingNatBool)).pair (vectorsExecutes [0,2])).comp
    (StructuralListMachine.exactExecutes EncodedTable.vectorEncoding)

def phasesExecutes : Executes encodingNatBool phaseListEncoding phases := by
  let pairs := ((vectorsExecutes [0,1,2,3]).pair matricesExecutes).comp
    (Executes.ofComputes (RootSearchDriver.crossComputes EncodedTable.vectorEncoding EncodedTable.matrixEncoding))
  exact ((Executes.ofComputes (constantComputes encodingNatBool EncodedTable.vectorEncoding [0,1,2,3])).pair pairs).comp
    (Executes.ofComputes (RootSearchDriver.crossComputes ResidueCells.encoding4
      (pairEncoding EncodedTable.vectorEncoding EncodedTable.matrixEncoding)))

def executes : Executes encodingNatBool outputEncoding templates := by
  let bodies := (supportsExecutes.pair phasesExecutes).comp
    (Executes.ofComputes (RootSearchDriver.crossComputes EncodedTable.rowsEncoding EncodedTable.phaseEncoding))
  let arity := StructuralListMachine.ofFinite RootSearchDriver.Height.binaryToUnary
  let cell : Executes (pairEncoding UnaryBinary.unaryEncoding
      (pairEncoding EncodedTable.rowsEncoding EncodedTable.phaseEncoding)) EncodedTable.encoding
      (fun p => p) := Executes.ofComputes (identityComputes EncodedTable.encoding)
  exact (arity.pair bodies).comp (Executes.mapList UnaryBinary.unaryEncoding
    (pairEncoding EncodedTable.rowsEncoding EncodedTable.phaseEncoding) EncodedTable.encoding
    (fun n p => (n,p)) cell)

def outputs (n : ℕ) : TM2OutputsInTime executes.machine.computer
    (encodingNatBool.encode n) (some (outputEncoding.encode (templates n))) (executes.cost n) := executes.outputs n
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RawAffineEnumeration
