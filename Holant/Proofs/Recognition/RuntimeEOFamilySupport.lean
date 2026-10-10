import Holant.Proofs.Recognition.RuntimeEOLabelSupport
import Holant.Proofs.Recognition.RuntimeEOResultSummary
import Holant.Proofs.Recognition.RuntimeEOProfiles

/-! One runtime label controller for all central or completed EO support views.
Original arities are read from the original family, masks/layers from the
runtime mode/profile, and zero packets from the one retained original support
table. All actual bad-word/triple lists and original labels are kept. The
public central entry computes that support table itself from original RootCodes.
Full template and profile aggregation remains a later composition. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOFamilySupport
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open PhysicalFolds
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Base := OriginalFamilyPackingMachine.Input × List RuntimeSupportTable.LabelPacket
abbrev baseEncoding := pairEncoding OriginalFamilyPackingMachine.encoding RuntimeSupportTable.resultEncoding
abbrev Mode := Bool × RuntimeEOProfiles.Profile
abbrev modeEncoding := pairEncoding encodingBoolBool RuntimeEOProfiles.profileEncoding
abbrev Context := Base × Mode
abbrev encoding := pairEncoding baseEncoding modeEncoding
abbrev LabelInput := Context × ℕ
abbrev labelInputEncoding := pairEncoding encoding encodingNatBool

def labels (r : Context) : List ℕ := List.range r.1.1.1.length
def labelArity (p : LabelInput) : ℕ := (p.1.1.1.1.getD p.2 (0,[])).1
def layer (p : LabelInput) : ℕ := p.1.2.2.getD p.2 0
def labelTable (p : LabelInput) : List RuntimeSupportTable.Packet := (p.1.1.2.getD p.2 (0,[])).2
def viewInput (p : LabelInput) : RuntimeEOViewSupport.Input :=
  ((labelArity p,p.1.2.1,layer p),labelTable p)
def labelOutput (p : LabelInput) : RuntimeEOResultSummary.LabelResult := (p.2,RuntimeEOLabelSupport.checks (viewInput p))
def output (r : Context) : List RuntimeEOResultSummary.LabelResult := (labels r).map (fun j => labelOutput (r,j))
def result (r : Context) := RuntimeEOResultSummary.finish (output r)

def base := RuntimeTensorRows.fst baseEncoding modeEncoding
def mode := RuntimeTensorRows.snd baseEncoding modeEncoding
def original := base.comp (RuntimeTensorRows.fst OriginalFamilyPackingMachine.encoding RuntimeSupportTable.resultEncoding)
def stored := base.comp (RuntimeTensorRows.snd OriginalFamilyPackingMachine.encoding RuntimeSupportTable.resultEncoding)
def originalFamily := original.comp (Executes.ofComputes OriginalFamilyPackingMachine.family)

def labelsExecutes : Executes encoding (framedListEncoding encodingNatBool) labels :=
  (originalFamily.comp (RuntimeTensorRows.length OriginalFamilyPackingMachine.vertexEncoding)).comp RationalInputMachine.Programs.range

def context := RuntimeTensorRows.fst encoding encodingNatBool
def index := RuntimeTensorRows.snd encoding encodingNatBool

def arityExecutes : Executes labelInputEncoding encodingNatBool labelArity :=
  (((context.comp originalFamily).pair index).comp
    (RuntimeTensorRows.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))).comp
      (RuntimeTensorRows.fst encodingNatBool CommonFieldMachine.rootsEncoding)

def layerExecutes : Executes labelInputEncoding encodingNatBool layer :=
  (((context.comp mode).comp (RuntimeTensorRows.snd encodingBoolBool RuntimeEOProfiles.profileEncoding)).pair index).comp
    (RuntimeTensorRows.lookup encodingNatBool 0)

def tableExecutes : Executes labelInputEncoding RuntimeSupportTable.labelResultEncoding labelTable :=
  (((context.comp stored).pair index).comp (RuntimeTensorRows.lookup RuntimeSupportTable.labelPacketEncoding (0,[]))).comp
    (RuntimeTensorRows.snd encodingNatBool RuntimeSupportTable.labelResultEncoding)

def viewExecutes : Executes labelInputEncoding RuntimeEOViewSupport.encoding viewInput :=
  (arityExecutes.pair
    (((context.comp mode).comp (RuntimeTensorRows.fst encodingBoolBool RuntimeEOProfiles.profileEncoding)).pair layerExecutes)).pair
      tableExecutes

def labelExecutes : Executes labelInputEncoding RuntimeEOResultSummary.labelEncoding labelOutput :=
  index.pair (viewExecutes.comp RuntimeEOLabelSupport.executes)

def executes : Executes encoding RuntimeEOResultSummary.familyEncoding output :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool RuntimeEOResultSummary.labelEncoding labelsExecutes
    (fun r j => labelOutput (r,j)) labelExecutes

def resultExecutes : Executes encoding RuntimeEOResultSummary.resultEncoding result :=
  executes.comp (Executes.ofComputes RuntimeEOResultSummary.computes)

/-- This index contains only the original represented family; its support
intermediate is the actual earlier programme output. -/
def sourceBase (d : RuntimeSupportTable.Data) : Base := (RuntimeSupportTable.original d,RuntimeSupportTable.output d)
def sourceContext (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile) : Context :=
  (sourceBase d,(complete,p))

def baseRuns : Runs OriginalFamilyPackingMachine.encoding baseEncoding RuntimeSupportTable.original sourceBase :=
  (Runs.ofComputes (identityComputes OriginalFamilyPackingMachine.encoding) RuntimeSupportTable.original).pair
    RuntimeSupportTable.executes

def central (d : RuntimeSupportTable.Data) := result (sourceContext d false [])
def centralRuns : Runs OriginalFamilyPackingMachine.encoding RuntimeEOResultSummary.resultEncoding
    RuntimeSupportTable.original central :=
  (baseRuns.after (pairComputes (identityComputes baseEncoding)
    (constantComputes baseEncoding modeEncoding (false,[])))).comp
      (RuntimeTensorEnumeration.ofExecutes resultExecutes (fun d => sourceContext d false []))

theorem labels_source (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile) :
    labels (sourceContext d complete p)=List.range d.count := by
  simp only [labels,sourceContext,sourceBase,RuntimeSupportTable.original,OriginalFamilyPackingSource.family_length]

theorem arity_source (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile) (i : Fin d.count) :
    labelArity (sourceContext d complete p,i.val)=d.arity i := by
  change (((List.finRange d.count).map
    (fun j => (d.arity j,(SparseTransform.allWords (d.arity j)).map (d.input j)))).getD i.val (0,[])).1=d.arity i
  rw [←List.ofFn_eq_map,PositiveCertificateMachine.getD_ofFn]

theorem table_source (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile) (i : Fin d.count) :
    labelTable (sourceContext d complete p,i.val)=RuntimeSupportTable.labelOutput ⟨d,i⟩ := by
  change ((RuntimeSupportTable.output d).getD i.val (0,[])).2=_
  rw [RuntimeSupportTable.stored_label]

theorem central_view_source (d : RuntimeSupportTable.Data) (i : Fin d.count) :
    viewInput (sourceContext d false [],i.val)=RuntimeEOLabelSupport.centralInput ⟨d,i⟩ := by
  unfold viewInput
  rw [arity_source,table_source]
  rfl

theorem completed_view_source (d : RuntimeSupportTable.Data) (p : RuntimeEOProfiles.Profile) (i : Fin d.count) :
    viewInput (sourceContext d true p,i.val)=RuntimeEOLabelSupport.completedInput ⟨d,i⟩ (p.getD i.val 0) := by
  unfold viewInput
  rw [arity_source,table_source]
  rfl

theorem stored_label (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile)
    (i : Fin d.count) :
    (output (sourceContext d complete p)).getD i.val (0,([],[],[]))=
      labelOutput (sourceContext d complete p,i.val) := by
  rw [output,labels_source,RuntimeTensorRowsSoundness.map_range_eq_ofFn,PositiveCertificateMachine.getD_ofFn]


theorem forall_source (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile)
    (P : RuntimeEOResultSummary.LabelResult → Prop) :
    (∀r∈output (sourceContext d complete p),P r) ↔
      ∀i : Fin d.count,P (labelOutput (sourceContext d complete p,i.val)) := by
  rw [output,labels_source]
  constructor
  · intro h i
    exact h _ (List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩)
  · intro h r hr
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
    exact h ⟨j,List.mem_range.mp hj⟩

theorem central_domain (d : RuntimeSupportTable.Data) : (central d).1.1=true ↔
    ∀i : Fin d.count,Signature.CentralSupport (RuntimeEOLabelSupport.centralSignature ⟨d,i⟩) := by
  change (RuntimeEOResultSummary.flags (output (sourceContext d false []))).1=true ↔ _
  rw [RuntimeEOResultSummary.domain_correct,forall_source]
  simp only [labelOutput,central_view_source,RuntimeEOLabelSupport.central_domain]

theorem completed_domain (d : RuntimeSupportTable.Data) (p : RuntimeEOProfiles.Profile) :
    (result (sourceContext d true p)).1.1=true ↔
      ∀i : Fin d.count,Signature.CentralSupport (RuntimeEOLabelSupport.completedSignature ⟨d,i⟩ (p.getD i.val 0)) := by
  change (RuntimeEOResultSummary.flags (output (sourceContext d true p))).1=true ↔ _
  rw [RuntimeEOResultSummary.domain_correct,forall_source]
  simp only [labelOutput,completed_view_source,RuntimeEOLabelSupport.completed_domain]

def signFlag (negative : Bool) (r : RuntimeEOResultSummary.Result) : Bool :=
  if negative then r.1.2.1 else r.1.2.2

theorem sign_flag_source (negative : Bool) (d : RuntimeSupportTable.Data) (complete : Bool) (p : RuntimeEOProfiles.Profile) :
    signFlag negative (result (sourceContext d complete p))=true ↔
      ∀i : Fin d.count,RuntimeEOLabelSupport.failures negative
        (RuntimeEOLabelSupport.checks (viewInput (sourceContext d complete p,i.val)))=[] := by
  cases negative
  · change (RuntimeEOResultSummary.flags (output (sourceContext d complete p))).2.2=true ↔ _
    rw [RuntimeEOResultSummary.negative_correct,forall_source]
    rfl
  · change (RuntimeEOResultSummary.flags (output (sourceContext d complete p))).2.1=true ↔ _
    rw [RuntimeEOResultSummary.positive_correct,forall_source]
    rfl

theorem central_sign (negative : Bool) (d : RuntimeSupportTable.Data) : signFlag negative (central d)=true ↔
    ∀i : Fin d.count,∀a b c,
      RuntimeEOLabelSupport.centralSignature ⟨d,i⟩ a≠0 →
      RuntimeEOLabelSupport.centralSignature ⟨d,i⟩ b≠0 →
      RuntimeEOLabelSupport.centralSignature ⟨d,i⟩ c≠0 →
      RuntimeEOLabelSupport.centralSignature ⟨d,i⟩ (tripleXor a b c)≠0 ∨
        0<(RuntimeEOSupportCorrectness.signOf negative).value*Holant.charge (tripleXor a b c) := by
  rw [central,sign_flag_source]
  simp only [central_view_source,RuntimeEOLabelSupport.central_sign]

theorem completed_sign (negative : Bool) (d : RuntimeSupportTable.Data) (p : RuntimeEOProfiles.Profile) :
    signFlag negative (result (sourceContext d true p))=true ↔
    ∀i : Fin d.count,∀a b c,
      RuntimeEOLabelSupport.completedSignature ⟨d,i⟩ (p.getD i.val 0) a≠0 →
      RuntimeEOLabelSupport.completedSignature ⟨d,i⟩ (p.getD i.val 0) b≠0 →
      RuntimeEOLabelSupport.completedSignature ⟨d,i⟩ (p.getD i.val 0) c≠0 →
      RuntimeEOLabelSupport.completedSignature ⟨d,i⟩ (p.getD i.val 0) (tripleXor a b c)≠0 ∨
        0<(RuntimeEOSupportCorrectness.signOf negative).value*Holant.charge (tripleXor a b c) := by
  rw [sign_flag_source]
  simp only [completed_view_source,RuntimeEOLabelSupport.completed_sign]

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeEOFamilySupport
