import Holant.Proofs.Recognition.RuntimeTensorAggregation
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorRequestSource
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorEnumeration

/-! One runtime candidate/label controller for every original arity layout.
The semantic index contains all layouts at once; the physical machine below
has no layout parameter. Every actual candidate result is retained in order.
The final flags are read from those stored option packets. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open PhysicalFolds
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest (Candidate candidateEncoding Context contextEncoding)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The entire arbitrary-layout promised source domain, erased from control. -/
abbrev Data := Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorAggregation.Data

def raw (d : Data) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.FamilyInput :=
  ((d.native,d.opposite),OriginalFamilyPackingSource.fromSource d.arity d.input false)
abbrev LabelData := Σ d : Data,Fin d.count

def labelContext (d : LabelData) : Context := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.atLabel (raw d.1,d.2.val)
def items (d : LabelData) : List Candidate := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidates (d.1.arity d.2)

theorem context_arity (d : LabelData) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.arity (labelContext d)=d.1.arity d.2 :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.arity_exact d.1.arity d.1.input d.1.native d.1.opposite d.2 _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.zeroCandidate

def candidateOutput (d : LabelData) (c : Candidate) : Option WitnessOutput.Output := by
  classical
  exact if h : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.Legal d.1.arity d.2 c then
    _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.output d.1.arity d.1.input d.1.native d.1.opposite d.2 c h d.1.G d.1.represented
  else none

abbrev Packet := Candidate × Option WitnessOutput.Output
abbrev packetEncoding := pairEncoding candidateEncoding WitnessOutput.resultEncoding
abbrev labelResultEncoding := framedListEncoding packetEncoding

def packet (d : LabelData) (c : Candidate) : Packet := (c,candidateOutput d c)
def labelOutput (d : LabelData) : List Packet := (items d).map (packet d)

abbrev CandidateCell := PromisedListMap.Cell items

theorem cellLegal (d : CandidateCell) : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.Legal d.1.1.arity d.1.2 d.2.val :=
  _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ d.2.property

def candidateRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding WitnessOutput.resultEncoding
    (PromisedListMap.cellInput labelContext items) (fun d : CandidateCell => candidateOutput d.1 d.2.val) where
  machine := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.machine
  cost d := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.cost d.1.1.arity d.1.1.input d.1.1.native d.1.1.opposite d.1.2 d.2.val
    (cellLegal d) d.1.1.G d.1.1.represented
  outputs d := by
    have h := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.execution d.1.1.arity d.1.1.input d.1.1.native d.1.1.opposite d.1.2 d.2.val
      (cellLegal d) d.1.1.G d.1.1.represented
    have hi : PromisedListMap.cellInput labelContext items d=
        _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.encode d.1.1.arity d.1.1.input d.1.1.native d.1.1.opposite d.1.2 d.2.val := rfl
    have ho : candidateOutput d.1 d.2.val = _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.output d.1.1.arity d.1.1.input
        d.1.1.native d.1.1.opposite d.1.2 d.2.val (cellLegal d) d.1.1.G d.1.1.represented := by
      simp only [candidateOutput,dif_pos (cellLegal d)]
    simpa only [hi,ho] using h

def packetRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.encoding packetEncoding
    (PromisedListMap.cellInput labelContext items) (fun d : CandidateCell => packet d.1 d.2.val) :=
  (Runs.ofComputes (Wiring.secondComputes contextEncoding candidateEncoding)
    (PromisedListMap.cellInput labelContext items)).pair candidateRuns

def itemsRuns : Runs contextEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidatesEncoding labelContext items :=
  (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.ofExecutes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.forContextExecutes labelContext).congr
    (fun d => congrArg _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidates (context_arity d))

def labelRuns : Runs contextEncoding labelResultEncoding labelContext labelOutput :=
  ((Runs.ofComputes (identityComputes contextEncoding) labelContext).pair itemsRuns).comp
    (PromisedListMap.mapList packetRuns)

/-- Reindexing changes correctness indices only, never machine syntax. -/
def reindexRuns {D D' A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {input : D → A} {output : D → B} (r : Runs ea eb input output) (f : D' → D) :
    Runs ea eb (fun d => input (f d)) (fun d => output (f d)) where
  machine := r.machine
  cost d := r.cost (f d)
  outputs d := r.outputs (f d)

def labels (d : Data) : List ℕ := List.range d.count
abbrev LabelPacket := ℕ × List Packet
abbrev labelPacketEncoding := pairEncoding encodingNatBool labelResultEncoding
abbrev familyResultEncoding := framedListEncoding labelPacketEncoding

def atLabelOutput (d : Data) (j : ℕ) : LabelPacket :=
  (j,if h : j<d.count then labelOutput ⟨d,⟨j,h⟩⟩ else [])
def familyOutput (d : Data) : List LabelPacket := (labels d).map (atLabelOutput d)

abbrev LabelCell := PromisedListMap.Cell labels

def labelData (d : LabelCell) : LabelData := ⟨d.1,⟨d.2.val,List.mem_range.mp d.2.property⟩⟩

abbrev labelInputEncoding := pairEncoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding encodingNatBool

def labelCellRuns : Runs labelInputEncoding labelPacketEncoding
    (PromisedListMap.cellInput raw labels) (fun d : LabelCell => atLabelOutput d.1 d.2.val) := by
  let contextRuns : Runs labelInputEncoding contextEncoding (PromisedListMap.cellInput raw labels)
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
    (fun d => _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.labels_source d.arity d.input (d.native,d.opposite))

/-- One physical two-level list controller, independent of count and arities. -/
def familyRuns : Runs _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding familyResultEncoding raw familyOutput :=
  ((Runs.ofComputes (identityComputes _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.familyEncoding) raw).pair labelsRuns).comp
    (PromisedListMap.mapList labelCellRuns)

def labelAccepted (ps : List Packet) : Bool := ps.any (fun p => p.2.isSome)
def familyAccepted (fs : List LabelPacket) : Bool := fs.all (fun p => labelAccepted p.2)

def labelAcceptedComputes : Computes labelResultEncoding encodingBoolBool labelAccepted :=
  congrComputes ((WireLists.mapComputes packetEncoding encodingBoolBool (fun p : Packet => p.2.isSome)
    ((Wiring.secondComputes candidateEncoding WitnessOutput.resultEncoding).andThen UniformTractXDecision.presence)).andThen
      ResidueCells.any) (fun xs => by simp only [labelAccepted,List.any_map,Function.comp_def,id_eq])

def familyAcceptedComputes : Computes familyResultEncoding encodingBoolBool familyAccepted :=
  congrComputes ((WireLists.mapComputes labelPacketEncoding encodingBoolBool (fun p : LabelPacket => labelAccepted p.2)
    ((Wiring.secondComputes encodingNatBool labelResultEncoding).andThen labelAcceptedComputes)).andThen
      ResidueCells.all) (fun xs => by simp only [familyAccepted,List.all_map,Function.comp_def,id_eq])


theorem candidate_correct (d : LabelData) (c : Candidate) (hc : c∈items d) :
    (candidateOutput d c).isSome=true ↔
      _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.CandidateTest d.1.arity d.1.native d.2 c
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ hc)
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed d.1.arity d.1.native d.1.opposite d.2 d.1.G) := by
  have hl : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.Legal d.1.arity d.2 c := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ hc
  simp only [candidateOutput,dif_pos hl]
  exact _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.output_correct d.1.arity d.1.input d.1.native d.1.opposite d.2 c
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ hc) d.1.G d.1.represented

theorem candidates_complete (d : LabelData) :
    (∃c∈items d,(candidateOutput d c).isSome=true) ↔
      RuntimeTensorRowsSoundness.RawFiniteTest d.1.native
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed d.1.arity d.1.native d.1.opposite d.2 d.1.G) := by
  constructor
  · rintro ⟨c,hc,ho⟩
    have ht := (candidate_correct d c hc).mp ho
    rcases (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.mem_candidates _ _).mp hc with rfl | ⟨hz,hg⟩
    · left
      simpa only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.CandidateTest,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.zeroCandidate,dite_true] using ht
    · right
      simp only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.CandidateTest,hz,Bool.false_eq_true,dite_false] at ht
      obtain ⟨hv,hbranch⟩ := ht
      exact ⟨c.2,hg,hv,hbranch⟩
  · rintro (hz | ⟨m,hg,hv,hbranch⟩)
    · have hc : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.zeroCandidate∈items d := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.zero_mem _
      refine ⟨_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.zeroCandidate,hc,?_⟩
      apply (candidate_correct d _ hc).mpr
      simpa only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.CandidateTest,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.zeroCandidate,dite_true] using hz
    · have hc : (false,m)∈items d := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.nonzero_mem _ m hg
      refine ⟨(false,m),hc,?_⟩
      apply (candidate_correct d _ hc).mpr
      simp only [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.CandidateTest,Bool.false_eq_true,dite_false]
      exact ⟨hv,hbranch⟩

theorem label_correct (d : LabelData) : labelAccepted (labelOutput d)=true ↔
    RuntimeTensorRowsSoundness.RawFiniteTest d.1.native
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed d.1.arity d.1.native d.1.opposite d.2 d.1.G) := by
  rw [←candidates_complete]
  simp only [labelAccepted,labelOutput,List.any_map,List.any_eq_true,packet,Function.comp_def]

theorem family_correct (d : Data) : familyAccepted (familyOutput d)=true ↔
    ∀i : Fin d.count,RuntimeTensorRowsSoundness.RawFiniteTest d.native
      (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed d.arity d.native d.opposite i d.G) := by
  simp only [familyAccepted,familyOutput,List.all_map,List.all_eq_true,labels,List.mem_range,Function.comp_def]
  constructor
  · intro h i
    apply (label_correct ⟨d,i⟩).mp
    simpa only [atLabelOutput,dif_pos i.isLt] using h i.val i.isLt
  · intro h j hj
    simp only [atLabelOutput,dif_pos hj]
    exact (label_correct ⟨d,⟨j,hj⟩⟩).mpr (h ⟨j,hj⟩)

def original (d : Data) : OriginalFamilyPackingMachine.Input :=
  OriginalFamilyPackingSource.fromSource d.arity d.input false

def withFlags (d : Data) (native opposite : Bool) : Data := {d with native:=native,opposite:=opposite}
def modeOutput (native opposite : Bool) (d : Data) : List LabelPacket := familyOutput (withFlags d native opposite)

def modeRuns (native opposite : Bool) : Runs OriginalFamilyPackingMachine.encoding familyResultEncoding
    original (modeOutput native opposite) :=
  (Runs.ofComputes (pairComputes
    (constantComputes OriginalFamilyPackingMachine.encoding _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequest.flagsEncoding (native,opposite))
    (identityComputes OriginalFamilyPackingMachine.encoding)) original).comp
      (reindexRuns familyRuns (fun d => withFlags d native opposite))

def family (d : Data) : SignatureFamily AlgebraicComplex := AffineBranch.indexedFamily d.G

theorem arity_mode_correct (d : Data) : familyAccepted (modeOutput false false d)=true ↔
    ArityTwoAlternative (family d) := by
  rw [modeOutput,family_correct]
  simp only [withFlags,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis,
    Bool.false_eq_true,ite_false,InvertibleKernel.identity_symm,InvertibleKernel.identity_action,
    ←RuntimeTensorRowsSoundness.arity_source_iff,ArityTwoAlternative,family,
    AffineBranch.indexedFamily,Set.forall_mem_range]

theorem matching_transform (opposite : Bool) {n : ℕ} (f : Signature AlgebraicComplex n) :
    (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis true opposite).symm.action f=
      (TensorDecisionMatching.basis opposite).symm.action (sourceKBasis.action f) := by
  cases opposite <;> simp [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.basis,TensorDecisionMatching.basis,
    InvertibleKernel.comp_symm,InvertibleKernel.comp_action,InvertibleKernel.symm_action_action]

theorem matching_mode_correct (opposite : Bool) (d : Data) :
    familyAccepted (modeOutput true opposite d)=true ↔
      ∀i : Fin d.count,SourceTensorClosure (matchingImage opposite) (sourceKBasis.action (d.G i)) := by
  rw [modeOutput,family_correct]
  simp only [withFlags,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.transformed,matching_transform,
    ←RuntimeTensorRowsSoundness.matching_source_iff]

abbrev Triple := List LabelPacket × (List LabelPacket × List LabelPacket)
abbrev tripleEncoding := pairEncoding familyResultEncoding (pairEncoding familyResultEncoding familyResultEncoding)

def triple (d : Data) : Triple := (modeOutput false false d,modeOutput true false d,modeOutput true true d)
def tripleRuns : Runs OriginalFamilyPackingMachine.encoding tripleEncoding original triple :=
  (modeRuns false false).pair ((modeRuns true false).pair (modeRuns true true))

abbrev Summary := Bool × (Bool × Bool)
abbrev summaryEncoding := pairEncoding encodingBoolBool (pairEncoding encodingBoolBool encodingBoolBool)

def summary (t : Triple) : Summary :=
  (familyAccepted t.1,familyAccepted t.2.1 || familyAccepted t.2.2,!(familyAccepted t.2.1))

def summaryComputes : Computes tripleEncoding summaryEncoding summary := by
  let a := (Wiring.firstComputes familyResultEncoding (pairEncoding familyResultEncoding familyResultEncoding)).andThen familyAcceptedComputes
  let rest := Wiring.secondComputes familyResultEncoding (pairEncoding familyResultEncoding familyResultEncoding)
  let left := (rest.andThen (Wiring.firstComputes familyResultEncoding familyResultEncoding)).andThen familyAcceptedComputes
  let right := (rest.andThen (Wiring.secondComputes familyResultEncoding familyResultEncoding)).andThen familyAcceptedComputes
  let op := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun p => p.1 || p.2)
  let neg := FiniteRecode.computes encodingBoolBool encodingBoolBool Bool.not 1 (fun b => by cases b <;> decide)
  exact pairComputes a (pairComputes ((pairComputes left right).andThen op) (left.andThen neg))

abbrev Output := Summary × Triple
abbrev outputEncoding := pairEncoding summaryEncoding tripleEncoding

def output (d : Data) : Output := (summary (triple d),triple d)

/-- All flags and the common matching orientation are computed from stored
packets. This finishing pass performs no algebraic search. -/
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding original output :=
  tripleRuns.after (pairComputes summaryComputes (identityComputes tripleEncoding))

theorem arity_correct (d : Data) : (output d).1.1=true ↔ ArityTwoAlternative (family d) :=
  arity_mode_correct d

theorem matching_correct (d : Data) : (output d).1.2.1=true ↔ MatchingAlternative (familyAction sourceKBasis (family d)) := by
  change (familyAccepted (modeOutput true false d) || familyAccepted (modeOutput true true d))=true ↔ _
  simp only [Bool.or_eq_true,matching_mode_correct,MatchingAlternative,family,familyAction,
    AffineBranch.indexedFamily,Set.forall_mem_image,Set.forall_mem_range]

theorem shared_orientation (d : Data) (h : (output d).1.2.1=true) :
    ∀i : Fin d.count,SourceTensorClosure (matchingImage (output d).1.2.2) (sourceKBasis.action (d.G i)) := by
  change (familyAccepted (modeOutput true false d) || familyAccepted (modeOutput true true d))=true at h
  have hh : familyAccepted (modeOutput true false d)=true ∨ familyAccepted (modeOutput true true d)=true := by
    simpa only [Bool.or_eq_true] using h
  cases hl : familyAccepted (modeOutput true false d) with
  | false =>
    have hr := hh.resolve_left (by simp only [hl,Bool.false_eq_true,not_false_eq_true])
    simpa only [output,summary,triple,hl,Bool.not_false] using (matching_mode_correct true d).mp hr
  | true =>
    simpa only [output,summary,triple,hl,Bool.not_true] using (matching_mode_correct false d).mp hl


theorem label_packet_mem (d : LabelData) (c : Candidate) (o : WitnessOutput.Output)
    (h : (c,some o)∈labelOutput d) : c∈items d ∧ candidateOutput d c=some o := by
  obtain ⟨c',hc,he⟩ := List.mem_map.mp h
  have hc' : c'=c := congrArg Prod.fst he
  subst c'
  exact ⟨hc,congrArg Prod.snd he⟩

/-- A retained positive packet comes from the actual checked algebraic search
candidate for its original family, label, metadata and common orientation. -/
theorem retained_packet (d : LabelData) (c : Candidate) (o : WitnessOutput.Output)
    (h : (c,some o)∈labelOutput d) :
    ∃hc : c∈items d,
      ∃a : OriginalSystemWitness.Candidate (m:=_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.Entries d.1.arity+2)
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.typedBody d.1.arity d.1.native d.1.opposite d.2 c
          (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ hc)),
      OriginalSystemWitness.candidate (UniformKPolynomial.descriptors d.1.arity d.1.input)
        (UniformKPolynomial.valid d.1.arity d.1.G d.1.input d.1.represented)
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.typedBody d.1.arity d.1.native d.1.opposite d.2 c
          (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ hc))
        (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.bindings d.1.arity)=some a ∧ o=WitnessOutput.ofCandidate a := by
  obtain ⟨hc,ho⟩ := label_packet_mem d c o h
  have hl : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.Legal d.1.arity d.2 c := _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorEnumeration.candidate_domain _ _ hc
  have hr : _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.output d.1.arity d.1.input d.1.native d.1.opposite d.2 c hl
      d.1.G d.1.represented=some o := by
    simpa only [candidateOutput,dif_pos hl] using ho
  exact ⟨hc,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.returned_packet d.1.arity d.1.input d.1.native d.1.opposite d.2 c hl
    d.1.G d.1.represented o hr⟩

theorem stored_label (d : Data) (i : Fin d.count) :
    (familyOutput d).getD i.val (0,[])=(i.val,labelOutput ⟨d,i⟩) := by
  rw [familyOutput,labels,RuntimeTensorRowsSoundness.map_range_eq_ofFn,PositiveCertificateMachine.getD_ofFn]
  simp only [atLabelOutput,dif_pos i.isLt]

/-- The only finishing machine reads stored results; it contains no second
criterion search phase. -/
theorem finishing_control : executes.machine = tripleRuns.machine.compose
    (pairComputes summaryComputes (identityComputes tripleEncoding)).machine := rfl

def source_outputs (d : Data) : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (original d))
    (some (outputEncoding.encode (output d))) (executes.cost d) := executes.outputs d

/-- One programme handles every represented runtime layout and returns both
criterion answers, a shared orientation, and all actual search packets. -/
theorem uniform_source : ∃M : BinaryCompose.Machine,∀d : Data,
    Nonempty (TM2OutputsInTime M.computer (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (outputEncoding.encode (output d))) (executes.cost d)) ∧
    ((output d).1.1=true ↔ ArityTwoAlternative (family d)) ∧
    ((output d).1.2.1=true ↔ MatchingAlternative (familyAction sourceKBasis (family d))) ∧
    ((output d).1.2.1=true → ∀i : Fin d.count,SourceTensorClosure (matchingImage (output d).1.2.2) (sourceKBasis.action (d.G i))) :=
  ⟨executes.machine,fun d => ⟨⟨executes.outputs d⟩,arity_correct d,matching_correct d,shared_orientation d⟩⟩

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
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorAggregation
