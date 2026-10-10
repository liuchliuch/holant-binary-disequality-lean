import Holant.Proofs.Recognition.RuntimeFourDecision
import Holant.Proofs.Recognition.UniformAugmentedNativeDecision

/-!
# Varying-layout equality-augmented native recognition

A fixed physical prepender inserts the prescribed binary equality RootCodes
before the one varying-layout ordinary/native four-clause programme. Its native
flag decides exactly `TractX (K (G ∪ {I}))`. The entire four-clause result,
including actual A/P/L packets and tensor/common-orientation packets, is kept.
Only original runtime arities and RootCode tables are supplied. Termination is
proved on their represented domain, with actual search-dependent clocks and
same-programme primitive/all-prefix bounds, not uniform polynomial recognition.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeAugmentedNativeDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open PhysicalFolds
open RuntimeTensorAggregation (Data original family)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev equalitySignature := UniformAugmentedNativeDecision.equalitySignature

def augment (d : Data) : Data where
  count := d.count+1
  arity := UniformAugmentedNativeDecision.augmentedArity d.arity
  input := (UniformAugmentedNativeDecision.augment d.arity (RuntimeFourDecision.legacy d)).input
  G := (UniformAugmentedNativeDecision.augment d.arity (RuntimeFourDecision.legacy d)).G
  represented := (UniformAugmentedNativeDecision.augment d.arity (RuntimeFourDecision.legacy d)).represented
  native := d.native
  opposite := d.opposite

theorem prepend_original (d : Data) :
    UniformAugmentedNativeDecision.prepend (original d)=original (augment d) :=
  UniformAugmentedNativeDecision.prepend_original d.arity (RuntimeFourDecision.legacy d)

theorem augmented_family (d : Data) : family (augment d)=family d ∪ {equalitySignature} :=
  UniformAugmentedNativeDecision.augmented_family d.arity (RuntimeFourDecision.legacy d)

abbrev Output := RuntimeFourDecision.Output
abbrev outputEncoding := RuntimeFourDecision.outputEncoding

def output (d : Data) : Output := RuntimeFourDecision.output (augment d)
def answer (d : Data) : Bool := (output d).1.2

/-- The programme is fixed before the count, layout and original RootCodes. -/
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding original output :=
  ((Runs.ofComputes UniformAugmentedNativeDecision.prependComputes original).congr prepend_original).comp
    (RuntimeTensorAggregation.reindexRuns RuntimeFourDecision.executes augment)

theorem answer_correct (d : Data) : answer d=true ↔
    TractX (familyAction sourceKBasis (family d ∪ {equalitySignature})) := by
  change (RuntimeFourDecision.output (augment d)).1.2=true ↔ _
  rw [RuntimeFourDecision.native_correct,augmented_family]

theorem answer_false_iff (d : Data) : answer d=false ↔
    ¬TractX (familyAction sourceKBasis (family d ∪ {equalitySignature})) := by
  have hb : ∀b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,answer_correct]

theorem ordinary_correct (d : Data) : (output d).1.1=true ↔ TractX (family d ∪ {equalitySignature}) := by
  change (RuntimeFourDecision.output (augment d)).1.1=true ↔ _
  rw [RuntimeFourDecision.ordinary_correct,augmented_family]

/-- All packets, including their root candidates and orientation, are retained
literally; the equality frontend performs no independent search. -/
theorem four_payload (d : Data) : output d=RuntimeFourDecision.output (augment d) := rfl

theorem tensor_payload (d : Data) : (output d).2.1=RuntimeTensorAggregation.output (augment d) := rfl

theorem native_packets (d : Data) : (output d).2.2.2=
    (RuntimeFourDecision.packet true .affine (augment d),
     RuntimeFourDecision.packet true .product (augment d),
     RuntimeFourDecision.packet true .localAffine (augment d)) := rfl

theorem matching_retained (d : Data) : (output d).2.1.1.2.1=true ↔
    MatchingAlternative (family d ∪ {equalitySignature}) := by
  change (RuntimeFourDecision.output (augment d)).2.1.1.2.1=true ↔ _
  rw [RuntimeFourDecision.matching_retained,augmented_family]

theorem matching_orientation (d : Data) (h : (output d).2.1.1.2.1=true) :
    ∀i : Fin (augment d).count,
      SourceTensorClosure (matchingImage (output d).2.1.1.2.2) ((augment d).G i) :=
  RuntimeFourDecision.matching_orientation (augment d) h

theorem control : executes.machine=UniformAugmentedNativeDecision.prependComputes.machine.compose
    RuntimeFourDecision.executes.machine := rfl

def source_outputs (d : Data) : TM2OutputsInTime executes.machine.computer
    (OriginalFamilyPackingMachine.encoding.encode (original d))
    (some (outputEncoding.encode (output d))) (executes.cost d) := executes.outputs d

theorem uniform_source : ∃M : BinaryCompose.Machine,∀d : Data,
    Nonempty (TM2OutputsInTime M.computer (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (outputEncoding.encode (output d))) (executes.cost d)) ∧
    (answer d=true ↔ TractX (familyAction sourceKBasis (family d ∪ {equalitySignature}))) ∧
    (answer d=false ↔ ¬TractX (familyAction sourceKBasis (family d ∪ {equalitySignature}))) :=
  ⟨executes.machine,fun d => ⟨⟨executes.outputs d⟩,answer_correct d,answer_false_iff d⟩⟩

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
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeAugmentedNativeDecision
