import Holant.Proofs.Recognition.RuntimeEOClassFamily
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOLiteralDecision
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOProfiles

/-! One runtime label/pairing controller for literal EO A/P classes. Every
pairing catalogue is generated from the central/completed view arity, and each
actual combined-system A/P packet is retained. The shared class flags are read
only after all label/pair packets have been stored. No pairing list, successful
template, transformed descriptor, or expected classification is source data. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOClassFamily
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open PhysicalFolds
open UniformTensorWitnessBranch (Metadata metadataEncoding)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRequest (Context contextEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

structure Data where
  family : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation.Data
  complete : Bool
  profile : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile

abbrev Mode := Bool × _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile
abbrev modeEncoding := pairEncoding encodingBoolBool _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.profileEncoding
abbrev Input := OriginalFamilyPackingMachine.Input × Mode
abbrev encoding := pairEncoding OriginalFamilyPackingMachine.encoding modeEncoding

def raw (d : Data) : Input := (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation.original d.family,d.complete,d.profile)
abbrev LabelData := Σd : Data,Fin d.family.count

def atLabel (p : Input × ℕ) : Context := (p.1.1,p.2,p.1.2.1,p.1.2.2.getD p.2 0)
def context (d : LabelData) : Context := atLabel (raw d.1,d.2.val)
def view (r : Context) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.View := ((r.1.1.getD r.2.1 (0,[])).1,r.2.2.1,r.2.2.2)
def items (d : LabelData) : List Metadata := RuntimeEOPairings.catalogue
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (d.1.family.arity d.2,d.1.complete,d.1.profile.getD d.2.val 0))

def atLabelExecutes : Executes (pairEncoding encoding encodingNatBool) contextEncoding atLabel := by
  let r := RuntimeTensorRows.fst encoding encodingNatBool
  let j := RuntimeTensorRows.snd encoding encodingNatBool
  let source := r.comp (RuntimeTensorRows.fst OriginalFamilyPackingMachine.encoding modeEncoding)
  let mode := r.comp (RuntimeTensorRows.snd OriginalFamilyPackingMachine.encoding modeEncoding)
  let complete := mode.comp (RuntimeTensorRows.fst encodingBoolBool _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.profileEncoding)
  let profile := mode.comp (RuntimeTensorRows.snd encodingBoolBool _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.profileEncoding)
  let layer := (profile.pair j).comp (RuntimeTensorRows.lookup encodingNatBool 0)
  exact source.pair (j.pair (complete.pair layer))

def viewExecutes : Executes contextEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewEncoding view := by
  let source := RuntimeTensorRows.fst OriginalFamilyPackingMachine.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRequest.selectionEncoding
  let sel := RuntimeTensorRows.snd OriginalFamilyPackingMachine.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRequest.selectionEncoding
  let label := sel.comp (RuntimeTensorRows.fst encodingNatBool _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewTailEncoding)
  let mode := sel.comp (RuntimeTensorRows.snd encodingNatBool _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.viewTailEncoding)
  let family := source.comp (Executes.ofComputes OriginalFamilyPackingMachine.family)
  let n := ((family.pair label).comp (RuntimeTensorRows.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))).comp
    (RuntimeTensorRows.fst encodingNatBool CommonFieldMachine.rootsEncoding)
  exact n.pair mode

def itemsExecutes : Executes contextEncoding RuntimeTensorCatalogue.catalogueEncoding
    (fun r => RuntimeEOPairings.catalogue (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (view r))) :=
  (viewExecutes.comp (Executes.ofComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arityComputes)).comp RuntimeEOPairings.catalogueExecutes

theorem view_source (d : LabelData) : view (context d)=
    (d.1.family.arity d.2,d.1.complete,d.1.profile.getD d.2.val 0) := by
  apply Prod.ext
  · change (((List.finRange d.1.family.count).map (fun i =>
      (d.1.family.arity i,(SparseTransform.allWords (d.1.family.arity i)).map (d.1.family.input i)))).getD d.2.val (0,[])).1=_
    rw [←List.ofFn_eq_map,PositiveCertificateMachine.getD_ofFn]
  · rfl

abbrev Cell := PromisedListMap.Cell items

def cellData (d : Cell) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.Data where
  family := d.1.1.family
  label := d.1.2
  complete := d.1.1.complete
  layer := d.1.1.profile.getD d.1.2.val 0
  metadata := d.2.val
  generated := d.2.property

def packet (d : LabelData) (m : Metadata) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.Output :=
  if h : m∈items d then _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.output (cellData ⟨d,⟨m,h⟩⟩)
  else ((false,false),(m,none,none))

def cellRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRequest.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.outputEncoding
    (PromisedListMap.cellInput context items) (fun d : Cell => packet d.1 d.2.val) where
  machine := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.executes.machine
  cost d := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.executes.cost (cellData d)
  outputs d := by
    have h := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.executes.outputs (cellData d)
    have hi : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.source (cellData d)=PromisedListMap.cellInput context items d := rfl
    have ho : packet d.1 d.2.val=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.output (cellData d) := by
      simp only [packet,dif_pos d.2.property]
    simpa only [hi,ho] using h

def itemsRuns : Runs contextEncoding RuntimeTensorCatalogue.catalogueEncoding context items :=
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.ofExecutes itemsExecutes context).congr
    (fun d => congrArg (fun v => RuntimeEOPairings.catalogue (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity v)) (view_source d))

abbrev LabelPackets := List _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.Output
abbrev labelPacketsEncoding := framedListEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.outputEncoding

def labelPackets (d : LabelData) : LabelPackets := (items d).map (packet d)
def labelRuns : Runs contextEncoding labelPacketsEncoding context labelPackets :=
  ((Runs.ofComputes (identityComputes contextEncoding) context).pair itemsRuns).comp (PromisedListMap.mapList cellRuns)

abbrev LabelResult := ℕ × LabelPackets
abbrev labelResultEncoding := pairEncoding encodingNatBool labelPacketsEncoding
abbrev resultEncoding := framedListEncoding labelResultEncoding

def labels (d : Data) : List ℕ := List.range d.family.count
def labelResult (d : Data) (j : ℕ) : LabelResult :=
  (j,if h : j<d.family.count then labelPackets ⟨d,⟨j,h⟩⟩ else [])
def output (d : Data) : List LabelResult := (labels d).map (labelResult d)
abbrev LabelCell := PromisedListMap.Cell labels

def labelData (d : LabelCell) : LabelData := ⟨d.1,⟨d.2.val,List.mem_range.mp d.2.property⟩⟩

def labelCellRuns : Runs (pairEncoding encoding encodingNatBool) labelResultEncoding
    (PromisedListMap.cellInput raw labels) (fun d : LabelCell => labelResult d.1 d.2.val) := by
  let contexts := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.ofExecutes atLabelExecutes (PromisedListMap.cellInput raw labels)
  let inner := contexts.comp (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation.reindexRuns labelRuns labelData)
  let j := Runs.ofComputes (Wiring.secondComputes encoding encodingNatBool) (PromisedListMap.cellInput raw labels)
  exact (j.pair inner).congr (fun d => by
    simp only [labelResult,dif_pos (List.mem_range.mp d.2.property)]
    rfl)

def labelsExecutes : Executes encoding (framedListEncoding encodingNatBool) (fun r => List.range r.1.1.length) :=
  (((RuntimeTensorRows.fst OriginalFamilyPackingMachine.encoding modeEncoding).comp
    (Executes.ofComputes OriginalFamilyPackingMachine.family)).comp
      (RuntimeTensorRows.length OriginalFamilyPackingMachine.vertexEncoding)).comp RationalInputMachine.Programs.range

def labelsRuns : Runs encoding (framedListEncoding encodingNatBool) raw labels :=
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.ofExecutes labelsExecutes raw).congr
    (fun d => by simp only [raw,labels,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation.original,OriginalFamilyPackingSource.family_length])

def executes : Runs encoding resultEncoding raw output :=
  ((Runs.ofComputes (identityComputes encoding) raw).pair labelsRuns).comp (PromisedListMap.mapList labelCellRuns)


def viewArity (d : LabelData) := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (d.1.family.arity d.2,d.1.complete,d.1.profile.getD d.2.val 0)
def viewSignature (d : LabelData) := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewSignature (d.1.family.G d.2)
  d.1.complete (d.1.profile.getD d.2.val 0)
def pairing (d : LabelData) (m : Metadata) (hm : m∈items d) : OrientedPerfectPairing (viewArity d) :=
  RuntimeEOPairings.pairing m ((RuntimeEOPairings.mem_catalogue _ _).mp hm).1
    ((RuntimeEOPairings.mem_catalogue _ _).mp hm).2

def classHolds (product : Bool) {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  if product then Product f else Affine f
def flag (product : Bool) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.Output) : Bool := if product then p.1.2 else p.1.1

theorem packet_correct (product : Bool) (d : LabelData) (m : Metadata) (hm : m∈items d) :
    flag product (packet d m)=true ↔ classHolds product ((pairing d m hm).restrict (viewSignature d)) := by
  simp only [packet,dif_pos hm]
  cases product
  · exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.affine_correct (cellData ⟨d,⟨m,hm⟩⟩)
  · exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.product_correct (cellData ⟨d,⟨m,hm⟩⟩)

def labelFlag (product : Bool) (ps : LabelPackets) : Bool := ps.all (flag product)
def familyFlag (product : Bool) (rs : List LabelResult) : Bool := rs.all (fun r => labelFlag product r.2)

theorem label_correct (product : Bool) (d : LabelData) : labelFlag product (labelPackets d)=true ↔
    ∀p : OrientedPerfectPairing (viewArity d),classHolds product (p.restrict (viewSignature d)) := by
  constructor
  · intro h p
    have hm : RuntimeEOPairings.source p∈items d := RuntimeEOPairings.source_catalogue p
    have hp := List.all_eq_true.mp h (packet d (RuntimeEOPairings.source p)) (List.mem_map.mpr ⟨_,hm,rfl⟩)
    have hc := (packet_correct product d _ hm).mp hp
    have he : pairing d (RuntimeEOPairings.source p) hm=p := RuntimeEOPairings.source_roundtrip p
    rw [he] at hc
    exact hc
  · intro h
    apply List.all_eq_true.mpr
    intro r hr
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
    exact (packet_correct product d m hm).mpr (h (pairing d m hm))

theorem family_correct (product : Bool) (d : Data) : familyFlag product (output d)=true ↔
    ∀i : Fin d.family.count,∀p : OrientedPerfectPairing (viewArity ⟨d,i⟩),
      classHolds product (p.restrict (viewSignature ⟨d,i⟩)) := by
  constructor
  · intro h i
    have hm : labelResult d i.val∈output d := List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩
    have hh := List.all_eq_true.mp h _ hm
    have hl : labelFlag product (labelPackets ⟨d,i⟩)=true := by
      simpa only [labelResult,dif_pos i.isLt] using hh
    exact (label_correct product ⟨d,i⟩).mp hl
  · intro h
    apply List.all_eq_true.mpr
    intro r hr
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
    have hj' : j<d.family.count := List.mem_range.mp hj
    simp only [labelResult,dif_pos hj']
    exact (label_correct product ⟨d,⟨j,hj'⟩⟩).mpr (h ⟨j,hj'⟩)

def flagComputes (product : Bool) : Computes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.outputEncoding encodingBoolBool (flag product) := by
  let flags := Wiring.firstComputes (pairEncoding encodingBoolBool encodingBoolBool) _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.detailsEncoding
  cases product
  · exact flags.andThen (Wiring.firstComputes encodingBoolBool encodingBoolBool)
  · exact flags.andThen (Wiring.secondComputes encodingBoolBool encodingBoolBool)

def labelFlagComputes (product : Bool) : Computes labelPacketsEncoding encodingBoolBool (labelFlag product) :=
  congrComputes ((WireLists.mapComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.outputEncoding encodingBoolBool (flag product)
    (flagComputes product)).andThen ResidueCells.all)
      (fun ps => by simp only [labelFlag,List.all_map,Function.comp_def,id_eq])

def familyFlagComputes (product : Bool) : Computes resultEncoding encodingBoolBool (familyFlag product) :=
  congrComputes ((WireLists.mapComputes labelResultEncoding encodingBoolBool (fun r => labelFlag product r.2)
    ((Wiring.secondComputes encodingNatBool labelPacketsEncoding).andThen (labelFlagComputes product))).andThen ResidueCells.all)
      (fun rs => by simp only [familyFlag,List.all_map,Function.comp_def,id_eq])

abbrev Summary := Bool × Bool
abbrev summaryEncoding := pairEncoding encodingBoolBool encodingBoolBool
abbrev Result := Summary × List LabelResult
abbrev finalEncoding := pairEncoding summaryEncoding resultEncoding

def finish (rs : List LabelResult) : Result := ((familyFlag false rs,familyFlag true rs),rs)
def finishComputes : Computes resultEncoding finalEncoding finish :=
  pairComputes (pairComputes (familyFlagComputes false) (familyFlagComputes true)) (identityComputes resultEncoding)
def result (d : Data) : Result := finish (output d)
def resultRuns : Runs encoding finalEncoding raw result := executes.after finishComputes

theorem affine_correct (d : Data) : (result d).1.1=true ↔
    ∀i : Fin d.family.count,∀p : OrientedPerfectPairing (viewArity ⟨d,i⟩),Affine (p.restrict (viewSignature ⟨d,i⟩)) :=
  family_correct false d

theorem product_correct (d : Data) : (result d).1.2=true ↔
    ∀i : Fin d.family.count,∀p : OrientedPerfectPairing (viewArity ⟨d,i⟩),Product (p.restrict (viewSignature ⟨d,i⟩)) :=
  family_correct true d

theorem retained (d : Data) : (result d).2=output d := rfl

theorem stored_label (d : Data) (i : Fin d.family.count) :
    (output d).getD i.val (0,[])=(i.val,labelPackets ⟨d,i⟩) := by
  rw [output,labels,RuntimeTensorRowsSoundness.map_range_eq_ofFn,PositiveCertificateMachine.getD_ofFn]
  simp only [labelResult,dif_pos i.isLt]

theorem stored_pair (d : LabelData) (m : Metadata) (hm : m∈items d) :
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralDecision.output (cellData ⟨d,⟨m,hm⟩⟩)∈labelPackets d := by
  apply List.mem_map.mpr
  refine ⟨m,hm,?_⟩
  simp only [packet,dif_pos hm]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOClassFamily
