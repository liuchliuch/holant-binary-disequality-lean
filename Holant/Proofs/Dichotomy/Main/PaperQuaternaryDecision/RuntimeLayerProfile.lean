import Holant.Proofs.Recognition.RuntimeLayerProfile
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOFamilySupport

/-! One physical all-label layer-profile checker on the stored original
support packets. Layer bounds/catalogues are produced by _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles;
this intermediate checker records every original label, proposed layer and
same-table test flag, then reads their conjunction. It reruns no root search. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeLayerProfile
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine (Executes)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOFamilySupport (Base baseEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev Input := Base × _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile
abbrev encoding := pairEncoding baseEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.profileEncoding
abbrev LabelInput := Input × ℕ
abbrev labelInputEncoding := pairEncoding encoding encodingNatBool
abbrev Row := ℕ × (ℕ × Bool)
abbrev rowTailEncoding := pairEncoding encodingNatBool encodingBoolBool
abbrev rowEncoding := pairEncoding encodingNatBool rowTailEncoding
abbrev rowsEncoding := framedListEncoding rowEncoding
abbrev Output := Bool × List Row
abbrev outputEncoding := pairEncoding encodingBoolBool rowsEncoding

def labels (r : Input) : List ℕ := List.range r.1.1.1.length
def layer (p : LabelInput) : ℕ := p.1.2.getD p.2 0
def table (p : LabelInput) : List _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Packet := (p.1.1.2.getD p.2 (0,[])).2
def row (p : LabelInput) : Row := (p.2,layer p,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.layer (layer p) (table p))
def rows (r : Input) : List Row := (labels r).map (fun j => row (r,j))
def accepted (rs : List Row) : Bool := rs.all (fun p => p.2.2)
def output (r : Input) : Output := (accepted (rows r),rows r)

def base := RuntimeTensorRows.fst baseEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.profileEncoding
def profile := RuntimeTensorRows.snd baseEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.profileEncoding
def original := base.comp (RuntimeTensorRows.fst OriginalFamilyPackingMachine.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.resultEncoding)
def stored := base.comp (RuntimeTensorRows.snd OriginalFamilyPackingMachine.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.resultEncoding)

def labelsExecutes : Executes encoding (framedListEncoding encodingNatBool) labels :=
  ((original.comp (Executes.ofComputes OriginalFamilyPackingMachine.family)).comp
    (RuntimeTensorRows.length OriginalFamilyPackingMachine.vertexEncoding)).comp RationalInputMachine.Programs.range

def ctx := RuntimeTensorRows.fst encoding encodingNatBool
def index := RuntimeTensorRows.snd encoding encodingNatBool

def layerExecutes : Executes labelInputEncoding encodingNatBool layer :=
  ((ctx.comp profile).pair index).comp (RuntimeTensorRows.lookup encodingNatBool 0)
def tableExecutes : Executes labelInputEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelResultEncoding table :=
  (((ctx.comp stored).pair index).comp (RuntimeTensorRows.lookup _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelPacketEncoding (0,[]))).comp
    (RuntimeTensorRows.snd encodingNatBool _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelResultEncoding)
def rowExecutes : Executes labelInputEncoding rowEncoding row :=
  index.pair (layerExecutes.pair ((layerExecutes.pair tableExecutes).comp _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.layerExecutes))
def rowsExecutes : Executes encoding rowsEncoding rows :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool rowEncoding labelsExecutes (fun r j => row (r,j)) rowExecutes

def acceptedComputes : Computes rowsEncoding encodingBoolBool accepted :=
  congrComputes ((WireLists.mapComputes rowEncoding encodingBoolBool (fun p => p.2.2)
    ((Wiring.secondComputes encodingNatBool rowTailEncoding).andThen (Wiring.secondComputes encodingNatBool encodingBoolBool))).andThen
      ResidueCells.all) (fun rs => by simp only [accepted,List.all_map,Function.comp_def,id_eq])

def executes : Executes encoding outputEncoding output :=
  rowsExecutes.comp (Executes.ofComputes (pairComputes acceptedComputes (identityComputes rowsEncoding)))

def source (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Data) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile) : Input := (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOFamilySupport.sourceBase d,p)

theorem labels_source (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Data) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile) :
    labels (source d p)=List.range d.count := by
  simp only [labels,source,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOFamilySupport.sourceBase,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.original,OriginalFamilyPackingSource.family_length]

theorem table_source (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Data) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile) (i : Fin d.count) :
    table (source d p,i.val)=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.labelOutput ⟨d,i⟩ := by
  change ((_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.output d).getD i.val (0,[])).2=_
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.stored_label]

theorem row_source (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Data) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile) (i : Fin d.count) :
    (row (source d p,i.val)).2.2=true ↔
      Signature.SingleLayer ((d.G i)) (p.getD i.val 0) := by
  change _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.layer (layer (source d p,i.val)) (table (source d p,i.val))=true ↔ _
  rw [table_source]
  exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportFlags.label_layer_correct (p.getD i.val 0) ⟨d,i⟩

theorem output_correct (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Data) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile) :
    (output (source d p)).1=true ↔
      ∀i : Fin d.count,Signature.SingleLayer ((d.G i)) (p.getD i.val 0) := by
  change (rows (source d p)).all (fun r => r.2.2)=true ↔ _
  rw [rows,labels_source,List.all_map,List.all_eq_true]
  constructor
  · intro h i
    exact (row_source d p i).mp (h i.val (List.mem_range.mpr i.isLt))
  · intro h j hj
    exact (row_source d p ⟨j,List.mem_range.mp hj⟩).mpr (h ⟨j,List.mem_range.mp hj⟩)

theorem stored_label (d : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeSupportTable.Data) (p : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOProfiles.Profile) (i : Fin d.count) :
    (output (source d p)).2.getD i.val (0,0,false)=row (source d p,i.val) := by
  change (rows (source d p)).getD i.val (0,0,false)=_
  rw [rows,labels_source,RuntimeTensorRowsSoundness.map_range_eq_ofFn,PositiveCertificateMachine.getD_ofFn]

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeLayerProfile
