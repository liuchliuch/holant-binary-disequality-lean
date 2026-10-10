import Holant.Proofs.Recognition.RuntimeTensorAggregation
import Holant.Proofs.Recognition.UniformNativeTractXWitness

/-!
# One varying-layout ordinary and native four-clause recognizer

Original runtime arities and RootCode tables are the only varying physical
source data. The arity-independent A/P/L raw-system/search programmes are
composed with the single runtime tensor programme. All six actual algebraic
packets and the complete tensor/common-orientation payload are retained once;
ordinary and native flags are read from that same stored output.

The theorem gives terminating recognition with actual search-dependent clocks
and same-programme primitive/prefix bounds. It does NOT give uniform polynomial
recognition. No padded catalogue, stopping height, termination certificate,
transformed RootCode, successful basis or desired answer is an input.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeFourDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open PhysicalFolds
open RuntimeTensorAggregation (Data original family)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev Kind := UniformTractXWitness.Kind
abbrev Witness := Option WitnessOutput.Output
abbrev witnessEncoding := WitnessOutput.resultEncoding
abbrev Triple := Witness × (Witness × Witness)
abbrev tripleEncoding := UniformTractXDecision.witnessTripleEncoding

def legacy (d : Data) : UniformTensorDecisionBranch.Data d.count d.arity :=
  ⟨d.input,d.G,d.represented⟩

def packet (native : Bool) (kind : Kind) (d : Data) : Witness :=
  if native then UniformNativeTractXWitness.output d.arity kind (legacy d)
  else UniformTractXWitness.output d.arity kind (legacy d)

/-- Class and ordinary/native tags are the only programme parameters. Neither
family count nor arity layout appears in its finite control. -/
def packetMachine (native : Bool) (kind : Kind) : BinaryCompose.Machine :=
  if native then UniformNativeTractXWitness.machine kind else UniformTractXWitness.machine kind

theorem packet_outputs (native : Bool) (kind : Kind) (d : Data) : ∃ticks,
    Nonempty (TM2OutputsInTime (packetMachine native kind).computer
      (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (witnessEncoding.encode (packet native kind d))) ticks) := by
  cases native
  · exact UniformTractXWitness.outputs d.arity kind (legacy d)
  · exact UniformNativeTractXWitness.outputs d.arity kind (legacy d)

def packetRuns (native : Bool) (kind : Kind) : Runs OriginalFamilyPackingMachine.encoding witnessEncoding
    original (packet native kind) where
  machine := packetMachine native kind
  cost d := Classical.choose (packet_outputs native kind d)
  outputs d := Classical.choice (Classical.choose_spec (packet_outputs native kind d))

def targetFamily (native : Bool) (d : Data) : SignatureFamily AlgebraicComplex :=
  if native then familyAction sourceKBasis (family d) else family d

theorem packet_correct (native : Bool) (kind : Kind) (d : Data) :
    (packet native kind d).isSome=true ↔ CommonTransformable (UniformTractXWitness.target kind) (targetFamily native d) := by
  cases native
  · exact UniformTractXWitness.output_correct d.arity kind (legacy d)
  · exact UniformNativeTractXWitness.output_correct d.arity kind (legacy d)

def triple (native : Bool) (d : Data) : Triple :=
  (packet native .affine d,packet native .product d,packet native .localAffine d)
def tripleRuns (native : Bool) : Runs OriginalFamilyPackingMachine.encoding tripleEncoding original (triple native) :=
  (packetRuns native .affine).pair ((packetRuns native .product).pair (packetRuns native .localAffine))

abbrev Details := RuntimeTensorAggregation.Output × (Triple × Triple)
abbrev packetPairEncoding := pairEncoding tripleEncoding tripleEncoding
abbrev detailsEncoding := pairEncoding RuntimeTensorAggregation.outputEncoding packetPairEncoding

def details (d : Data) : Details := (RuntimeTensorAggregation.output d,triple false d,triple true d)
def detailsRuns : Runs OriginalFamilyPackingMachine.encoding detailsEncoding original details :=
  RuntimeTensorAggregation.executes.pair ((tripleRuns false).pair (tripleRuns true))

def flags (d : Details) : Bool × Bool :=
  (UniformTractXDecision.summary (d.1.1.1,d.2.1),UniformTractXDecision.summary (d.1.1.1,d.2.2))

def flagsComputes : Computes detailsEncoding (pairEncoding encodingBoolBool encodingBoolBool) flags := by
  let tensor := Wiring.firstComputes RuntimeTensorAggregation.outputEncoding packetPairEncoding
  let tensorSummary := tensor.andThen (Wiring.firstComputes RuntimeTensorAggregation.summaryEncoding RuntimeTensorAggregation.tripleEncoding)
  let tensorFlag := tensorSummary.andThen (Wiring.firstComputes encodingBoolBool (pairEncoding encodingBoolBool encodingBoolBool))
  let tail := Wiring.secondComputes RuntimeTensorAggregation.outputEncoding packetPairEncoding
  let ordinary := tail.andThen (Wiring.firstComputes tripleEncoding tripleEncoding)
  let native := tail.andThen (Wiring.secondComputes tripleEncoding tripleEncoding)
  exact pairComputes ((pairComputes tensorFlag ordinary).andThen UniformTractXDecision.summaryComputes)
    ((pairComputes tensorFlag native).andThen UniformTractXDecision.summaryComputes)

abbrev Output := (Bool × Bool) × Details
abbrev outputEncoding := pairEncoding (pairEncoding encodingBoolBool encodingBoolBool) detailsEncoding

def output (d : Data) : Output := (flags (details d),details d)

/-- The sole ordinary/native four-clause programme across all layouts. -/
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding original output :=
  detailsRuns.after (pairComputes flagsComputes (identityComputes detailsEncoding))

theorem tensor_native_correct (d : Data) : (RuntimeTensorAggregation.output d).1.1=true ↔
    ArityTwoAlternative (targetFamily true d) :=
  (RuntimeTensorAggregation.arity_correct d).trans (UniformNativeTractXSemantics.tensor_iff d.arity (legacy d))

theorem ordinary_correct (d : Data) : (output d).1.1=true ↔ TractX (family d) := by
  change (output d).1.1=true ↔ TractX (AffineBranch.indexedFamily (legacy d).G)
  rw [UniformTractXSemantics.tractX_iff_core d.arity (legacy d)]
  simp only [output,flags,details,triple,UniformTractXDecision.summary,Bool.or_eq_true,
    RuntimeTensorAggregation.arity_correct,packet_correct,UniformTractXWitness.target,
    targetFamily,Bool.false_eq_true,ite_false,TractXCore,or_assoc,RuntimeTensorAggregation.family,legacy]

theorem native_correct (d : Data) : (output d).1.2=true ↔ TractX (familyAction sourceKBasis (family d)) := by
  change (output d).1.2=true ↔ TractX (UniformNativeTractXSemantics.family d.arity (legacy d))
  rw [UniformNativeTractXSemantics.tractX_iff_core d.arity (legacy d)]
  simp only [output,flags,details,triple,UniformTractXDecision.summary,Bool.or_eq_true,
    tensor_native_correct,packet_correct,UniformTractXWitness.target,
    targetFamily,ite_true,TractXCore,or_assoc,RuntimeTensorAggregation.family,legacy,UniformNativeTractXSemantics.family]

theorem ordinary_false_iff (d : Data) : (output d).1.1=false ↔ ¬TractX (family d) := by
  have hb : ∀b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,ordinary_correct]

theorem native_false_iff (d : Data) : (output d).1.2=false ↔ ¬TractX (familyAction sourceKBasis (family d)) := by
  have hb : ∀b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,native_correct]

/-- The tensor and matching orientation channel is retained unchanged. -/
theorem tensor_payload (d : Data) : (output d).2.1=RuntimeTensorAggregation.output d := rfl

theorem matching_retained (d : Data) : (output d).2.1.1.2.1=true ↔ MatchingAlternative (family d) :=
  RuntimeTensorAggregation.matching_correct d

theorem matching_orientation (d : Data) (h : (output d).2.1.1.2.1=true) :
    ∀i : Fin d.count,SourceTensorClosure (matchingImage (output d).2.1.1.2.2) (d.G i) :=
  RuntimeTensorAggregation.shared_orientation d h

theorem ordinary_packets (d : Data) :
    (output d).2.2.1=(packet false .affine d,packet false .product d,packet false .localAffine d) := rfl

theorem native_packets (d : Data) :
    (output d).2.2.2=(packet true .affine d,packet true .product d,packet true .localAffine d) := rfl

/-- All six witness channels and the tensor channel are computed before the
flag pass. No criterion search is rerun by the final decision. -/
theorem finishing_control : executes.machine=detailsRuns.machine.compose
    (pairComputes flagsComputes (identityComputes detailsEncoding)).machine := rfl

def source_outputs (d : Data) : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (original d))
    (some (outputEncoding.encode (output d))) (executes.cost d) := executes.outputs d

theorem uniform_source : ∃M : BinaryCompose.Machine,∀d : Data,
    Nonempty (TM2OutputsInTime M.computer (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (outputEncoding.encode (output d))) (executes.cost d)) ∧
    ((output d).1.1=true ↔ TractX (family d)) ∧
    ((output d).1.2=true ↔ TractX (familyAction sourceKBasis (family d))) ∧
    ((output d).2.1.1.2.1=true ↔ MatchingAlternative (family d)) :=
  ⟨executes.machine,fun d => ⟨⟨executes.outputs d⟩,ordinary_correct d,native_correct d,matching_retained d⟩⟩

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

/-- The ordinary retained result is the original search candidate, including
its literal system and original coefficient binding layout. -/
theorem ordinary_returned_packet (kind : Kind) (d : Data) (o : WitnessOutput.Output)
    (ho : packet false kind d=some o) :
    ∃c : OriginalSystemWitness.Candidate (m:=UniformTractXWitness.Entries d.arity+2)
        (UniformTractXWitness.body d.arity kind d.input),
      OriginalSystemWitness.candidate (UniformTractXWitness.descriptors d.arity d.input)
        (UniformTractXWitness.descriptorValid d.arity (legacy d))
        (UniformTractXWitness.body d.arity kind d.input) (UniformTractXWitness.address d.arity kind)=some c ∧
      o=WitnessOutput.ofCandidate c := by
  obtain ⟨c,hc,ho,_⟩ := UniformTractXWitness.returned_sound d.arity kind (legacy d) o ho
  exact ⟨c,hc,ho⟩

/-- The native retained result keeps the actual native-edge search candidate;
no new basis or field point replaces the serialized coordinates. -/
theorem native_returned_packet (kind : Kind) (d : Data) (o : WitnessOutput.Output)
    (ho : packet true kind d=some o) :
    ∃c : OriginalSystemWitness.Candidate (m:=UniformNativeTractXWitness.Entries d.arity+2)
        (UniformNativeTractXWitness.body d.arity kind d.input),
      OriginalSystemWitness.candidate (UniformNativeTractXWitness.descriptors d.arity d.input)
        (UniformNativeTractXWitness.descriptorValid d.arity (legacy d))
        (UniformNativeTractXWitness.body d.arity kind d.input) (UniformNativeTractXWitness.address d.arity kind)=some c ∧
      o=WitnessOutput.ofCandidate c := by
  obtain ⟨c,hc,ho,_⟩ := UniformNativeTractXWitness.returned_sound d.arity kind (legacy d) o ho
  exact ⟨c,hc,ho⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeFourDecision
