import Holant.Proofs.Recognition.RuntimeSupportTable
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEntryProbe
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorEnumeration

/-! Runtime support tables for all original arity layouts. A nested physical
label/word controller invokes the same K-inverse entry programme and preserves
every returned algebraic packet beside its original label and Boolean word.
Only legal original RootCodes are promised; no evaluator or zero table is input.
This is support infrastructure, not the complete EO or seven-clause classifier. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open PhysicalFolds
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest (Context contextEncoding)
open RuntimeTensorRows (Word wordEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Data := Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSupportTable.Data

def original (d : Data) := OriginalFamilyPackingSource.fromSource d.arity d.input false
def raw (d : Data) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.FamilyInput := ((false,false),original d)
abbrev LabelData := Σ d : Data,Fin d.count

def labelContext (d : LabelData) : Context := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.atLabel (raw d.1,d.2.val)
def items (d : LabelData) : List Word := RationalTableMachine.words (d.1.arity d.2)

theorem context_arity (d : LabelData) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.arity (labelContext d)=d.1.arity d.2 :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.arity_exact d.1.arity d.1.input false false d.2 _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.dummy

theorem word_exists (d : LabelData) (w : Word) (h : w∈items d) :
    ∃x : Fin (d.1.arity d.2) → Bool,List.ofFn x=w := by
  rw [items,RationalTableMachine.words_eq] at h
  obtain ⟨x,_,hx⟩ := List.mem_map.mp h
  exact ⟨x,hx⟩

def reify (d : LabelData) (w : Word) (h : w∈items d) : Fin (d.1.arity d.2) → Bool :=
  Classical.choose (word_exists d w h)
theorem reify_exact (d : LabelData) (w : Word) (h : w∈items d) : List.ofFn (reify d w h)=w :=
  Classical.choose_spec (word_exists d w h)
theorem source_mem (d : LabelData) (x : Fin (d.1.arity d.2) → Bool) : List.ofFn x∈items d := by
  rw [items,RationalTableMachine.words_eq]
  exact List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩
theorem reify_source (d : LabelData) (x : Fin (d.1.arity d.2) → Bool) (h : List.ofFn x∈items d) :
    reify d (List.ofFn x) h=x := List.ofFn_inj.mp (reify_exact d (List.ofFn x) h)

def entryOutput (d : LabelData) (w : Word) : Option WitnessOutput.Output :=
  if h : w∈items d then _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.output d.1.arity d.1.input false false d.2
    (reify d w h) d.1.G d.1.represented else none
abbrev Packet := Word × Option WitnessOutput.Output
abbrev packetEncoding := pairEncoding wordEncoding WitnessOutput.resultEncoding
abbrev labelResultEncoding := framedListEncoding packetEncoding

def packet (d : LabelData) (w : Word) : Packet := (w,entryOutput d w)
def labelOutput (d : LabelData) : List Packet := (items d).map (packet d)
abbrev Cell := PromisedListMap.Cell items
abbrev cellEncoding := pairEncoding contextEncoding wordEncoding

def prepare (p : Context × Word) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.Input := ((p.1,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.dummy),p.2)
def prepareComputes : Computes cellEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.encoding prepare :=
  pairComputes (pairComputes (Wiring.firstComputes contextEncoding wordEncoding)
    (constantComputes cellEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.candidateEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.dummy))
      (Wiring.secondComputes contextEncoding wordEncoding)

def probeRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.encoding WitnessOutput.resultEncoding
    (fun d : Cell => prepare (PromisedListMap.cellInput labelContext items d))
    (fun d => entryOutput d.1 d.2.val) where
  machine := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.machine
  cost d := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.cost d.1.1.arity d.1.1.input false false d.1.2
    (reify d.1 d.2.val d.2.property) d.1.1.G d.1.1.represented
  outputs d := by
    have h := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.execution d.1.1.arity d.1.1.input false false d.1.2
      (reify d.1 d.2.val d.2.property) d.1.1.G d.1.1.represented
    have hi : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.encode d.1.1.arity d.1.1.input false false d.1.2
        (reify d.1 d.2.val d.2.property)=prepare (PromisedListMap.cellInput labelContext items d) := by
      unfold _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.encode
      rw [reify_exact]
      rfl
    have ho : entryOutput d.1 d.2.val=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.output d.1.1.arity d.1.1.input false false d.1.2
        (reify d.1 d.2.val d.2.property) d.1.1.G d.1.1.represented := by
      simp only [entryOutput,dif_pos d.2.property]
    simpa only [hi,ho] using h

def cellRuns : Runs cellEncoding packetEncoding (PromisedListMap.cellInput labelContext items)
    (fun d : Cell => packet d.1 d.2.val) :=
  (Runs.ofComputes (Wiring.secondComputes contextEncoding wordEncoding)
    (PromisedListMap.cellInput labelContext items)).pair
      ((Runs.ofComputes prepareComputes (PromisedListMap.cellInput labelContext items)).comp probeRuns)

def itemsRuns : Runs contextEncoding (framedListEncoding wordEncoding) labelContext items :=
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.ofExecutes
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.arityExecutes.comp RationalTableMachine.wordsExecutes) labelContext).congr
      (fun d => congrArg RationalTableMachine.words (context_arity d))

def labelRuns : Runs contextEncoding labelResultEncoding labelContext labelOutput :=
  ((Runs.ofComputes (identityComputes contextEncoding) labelContext).pair itemsRuns).comp
    (PromisedListMap.mapList cellRuns)

def reindexRuns {D D' A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {input : D → A} {output : D → B} (r : Runs ea eb input output) (f : D' → D) :
    Runs ea eb (fun d => input (f d)) (fun d => output (f d)) :=
  ⟨r.machine,fun d => r.cost (f d),fun d => r.outputs (f d)⟩

def labels (d : Data) := List.range d.count
abbrev LabelPacket := ℕ × List Packet
abbrev labelPacketEncoding := pairEncoding encodingNatBool labelResultEncoding
abbrev resultEncoding := framedListEncoding labelPacketEncoding

def atLabelOutput (d : Data) (j : ℕ) : LabelPacket :=
  (j,if h : j<d.count then labelOutput ⟨d,⟨j,h⟩⟩ else [])
def output (d : Data) : List LabelPacket := (labels d).map (atLabelOutput d)
abbrev LabelCell := PromisedListMap.Cell labels
abbrev labelCellEncoding := pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding encodingNatBool

def labelData (d : LabelCell) : LabelData := ⟨d.1,⟨d.2.val,List.mem_range.mp d.2.property⟩⟩

def labelCellRuns : Runs labelCellEncoding labelPacketEncoding
    (PromisedListMap.cellInput raw labels) (fun d : LabelCell => atLabelOutput d.1 d.2.val) := by
  let contextRuns : Runs labelCellEncoding contextEncoding (PromisedListMap.cellInput raw labels)
      (fun d => labelContext (labelData d)) :=
    Runs.ofComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.atLabelComputes (PromisedListMap.cellInput raw labels)
  let inner := contextRuns.comp (reindexRuns labelRuns labelData)
  let j := Runs.ofComputes (Wiring.secondComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding encodingNatBool)
    (PromisedListMap.cellInput raw labels)
  exact (j.pair inner).congr (fun d => by
    simp only [atLabelOutput,dif_pos (List.mem_range.mp d.2.property)]
    rfl)

def labelsRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.indexEncoding raw labels :=
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.ofExecutes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.labelsExecutes raw).congr
    (fun d => _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.labels_source d.arity d.input (false,false))

def familyRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding resultEncoding raw output :=
  ((Runs.ofComputes (identityComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding) raw).pair labelsRuns).comp
    (PromisedListMap.mapList labelCellRuns)

/-- Public machine input is the original family alone; prescribed K mode is generated. -/
def executes : Runs OriginalFamilyPackingMachine.encoding resultEncoding original output :=
  (Runs.ofComputes (pairComputes
    (constantComputes OriginalFamilyPackingMachine.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.flagsEncoding (false,false))
    (identityComputes OriginalFamilyPackingMachine.encoding)) original).comp familyRuns

theorem source_zero_correct (d : LabelData) (x : Fin (d.1.arity d.2) → Bool) :
    (entryOutput d (List.ofFn x)).isSome=true ↔ (d.1.G d.2) x=0 := by
  simp only [entryOutput,dif_pos (source_mem d x),reify_source]
  simpa only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis,
    ite_true,TensorDecisionMatching.basis,Bool.false_eq_true,ite_false,
    InvertibleKernel.identity_symm,InvertibleKernel.identity_action] using
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEntryProbe.output_correct d.1.arity d.1.input false false d.2 x d.1.G d.1.represented

/-- Every original label/word appears with the exact same retained root-search result. -/
theorem retained (d : Data) (i : Fin d.count) (x : Fin (d.arity i) → Bool) :
    (i.val,labelOutput ⟨d,i⟩)∈output d ∧
    (List.ofFn x,entryOutput ⟨d,i⟩ (List.ofFn x))∈labelOutput ⟨d,i⟩ := by
  constructor
  · apply List.mem_map.mpr
    refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
    simp only [atLabelOutput,dif_pos i.isLt]
  · exact List.mem_map.mpr ⟨List.ofFn x,source_mem ⟨d,i⟩ x,rfl⟩


theorem stored_label (d : Data) (i : Fin d.count) :
    (output d).getD i.val (0,[])=(i.val,labelOutput ⟨d,i⟩) := by
  rw [output,labels,RuntimeTensorRowsSoundness.map_range_eq_ofFn,PositiveCertificateMachine.getD_ofFn]
  simp only [atLabelOutput,dif_pos i.isLt]

def source_outputs (d : Data) : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (original d))
    (some (resultEncoding.encode (output d))) (executes.cost d) := executes.outputs d

/-- The programme quantifier precedes every arity/layout and coefficient input. -/
theorem uniform_source : ∃M : BinaryCompose.Machine,∀d : Data,
    Nonempty (TM2OutputsInTime M.computer (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (resultEncoding.encode (output d))) (executes.cost d)) ∧
    ∀i : Fin d.count,∀x : Fin (d.arity i) → Bool,
      (entryOutput ⟨d,i⟩ (List.ofFn x)).isSome=true ↔ (d.G i) x=0 :=
  ⟨executes.machine,fun d => ⟨⟨executes.outputs d⟩,fun i x => source_zero_correct ⟨d,i⟩ x⟩⟩

theorem resources (d : Data) :
    primitiveCost executes.machine (executes.outputs d).steps
      (some (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d)))) ≤
      executes.cost d*executes.machine.primitiveBudget ∧
    ∀k,k≤(executes.outputs d).steps → ∀cfg : executes.machine.Config,
      (fun st => st.bind executes.machine.computer.step)^[k]
        (some (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d))))=some cfg →
      stackSize cfg.stk ≤ (OriginalFamilyPackingMachine.encoding.encode (original d)).length+
        executes.cost d*executes.machine.primitiveBudget := by
  constructor
  · exact (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ (executes.outputs d).steps_le_m)
  · intro k hk cfg hc
    have h := executes.machine.run_size_le
      (initList executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d))) cfg k hc
    rw [Machine.size_init] at h
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hk.trans (executes.outputs d).steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable
