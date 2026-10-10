import Holant.Proofs.Recognition.UniformNativeTractXWitness
import Holant.Proofs.Recognition.UniformTensorWitnessFamily

/-!
# Physical exact decision of native TractX(K G)

This single programme reads the unchanged original RootCode-family word and
returns the positive/negative answer for the literal forward-source-K criterion.
The actual native A/P/L search packets are retained in the output, and the
ordered arity-two tensor certificates are emitted as an explicitly charged
companion run. A fixed recoder supplies the native disequality edge internally;
no transformed RootCode, chosen basis, coefficient field, accepted decomposition,
semantic evaluator or desired answer is input.

The original arity layout fixes the programme. Coefficient RootCodes vary at
runtime. The bounds below are finite actual-clock/primitive/all-prefix-storage
bounds, not polynomial recognition bounds or a varying-layout compiler.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformNativeTractXDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open PhysicalFolds UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Bundle := UniformTractXDecision.Bundle
abbrev bundleEncoding := UniformTractXDecision.bundleEncoding

def bundle (d : Data s arity) : Bundle :=
  (UniformTensorDecision.arityFamily arity d,
    UniformNativeTractXWitness.output arity .affine d,
    UniformNativeTractXWitness.output arity .product d,
    UniformNativeTractXWitness.output arity .localAffine d)

def bundleRuns : Runs OriginalFamilyPackingMachine.encoding bundleEncoding
    (original arity) (bundle arity) :=
  (UniformTensorDecision.arityFamilyRuns arity).pair
    ((UniformNativeTractXWitness.runs arity .affine).pair
      ((UniformNativeTractXWitness.runs arity .product).pair
        (UniformNativeTractXWitness.runs arity .localAffine)))

def answer (d : Data s arity) : Bool := UniformTractXDecision.summary (bundle arity d)
def answerRuns : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (answer arity) :=
  (bundleRuns arity).after UniformTractXDecision.summaryComputes

theorem tensor_correct (d : Data s arity) :
    UniformTensorDecision.arityFamily arity d=true ↔
      ArityTwoAlternative (UniformNativeTractXSemantics.family arity d) :=
  (UniformTensorDecision.arityAlternative_correct arity d).trans
    (UniformNativeTractXSemantics.tensor_iff arity d)

theorem answer_correct (d : Data s arity) :
    answer arity d=true ↔
      TractX (familyAction sourceKBasis (AffineBranch.indexedFamily d.G)) := by
  rw [UniformNativeTractXSemantics.tractX_iff_core arity d]
  simp only [answer,UniformTractXDecision.summary,bundle,Bool.or_eq_true,tensor_correct,
    UniformNativeTractXWitness.output_correct,UniformTractXWitness.target,TractXCore,or_assoc]

theorem answer_false_iff (d : Data s arity) :
    answer arity d=false ↔
      ¬TractX (familyAction sourceKBasis (AffineBranch.indexedFamily d.G)) := by
  have hb : ∀ b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,answer_correct]

/-- Actual native search packets and the ordered source-coordinate tensor packet.
Arity-two certificates transport by source K without manufacturing new roots. -/
abbrev detailsEncoding := pairEncoding bundleEncoding UniformTensorWitnessFamily.familyEncoding
def details (d : Data s arity) := (bundle arity d,UniformTensorWitnessFamily.arityFamily arity d)
def detailsRuns : Runs OriginalFamilyPackingMachine.encoding detailsEncoding
    (original arity) (details arity) :=
  (bundleRuns arity).pair (UniformTensorWitnessFamily.arityFamilyRuns arity)

abbrev outputEncoding := pairEncoding encodingBoolBool detailsEncoding
def output (d : Data s arity) := (answer arity d,details arity d)
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding (original arity) (output arity) :=
  (detailsRuns arity).after (pairComputes
    ((Wiring.firstComputes bundleEncoding UniformTensorWitnessFamily.familyEncoding).andThen
      UniformTractXDecision.summaryComputes) (identityComputes detailsEncoding))

theorem tensor_packets_correct (d : Data s arity) :
    (∀ c ∈ (output arity d).2.2,UniformTensorWitness.accepted c=true) ↔
      ArityTwoAlternative (familyAction sourceKBasis (AffineBranch.indexedFamily d.G)) :=
  (UniformTensorWitnessFamily.arityFamily_correct arity d).trans
    (UniformNativeTractXSemantics.tensor_iff arity d)

/-- Same programme, same original input and actual retained native witnesses. -/
theorem source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (executes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (outputEncoding.encode (output arity d))) ((executes arity).cost d)) ∧
    ((output arity d).1=true ↔ TractX (familyAction sourceKBasis (AffineBranch.indexedFamily d.G))) ∧
    ((output arity d).1=false ↔ ¬TractX (familyAction sourceKBasis (AffineBranch.indexedFamily d.G))) ∧
    (((output arity d).2.1.2.1).isSome=true ↔
      CommonTransformable affineClass (familyAction sourceKBasis (AffineBranch.indexedFamily d.G))) ∧
    (((output arity d).2.1.2.2.1).isSome=true ↔
      CommonTransformable productClass (familyAction sourceKBasis (AffineBranch.indexedFamily d.G))) ∧
    (((output arity d).2.1.2.2.2).isSome=true ↔
      CommonTransformable localAffineClass (familyAction sourceKBasis (AffineBranch.indexedFamily d.G))) ∧
    ((∀ c ∈ (output arity d).2.2,UniformTensorWitness.accepted c=true) ↔
      ArityTwoAlternative (familyAction sourceKBasis (AffineBranch.indexedFamily d.G))) :=
  ⟨⟨(executes arity).outputs d⟩,answer_correct arity d,answer_false_iff arity d,
    UniformNativeTractXWitness.output_correct arity .affine d,
    UniformNativeTractXWitness.output_correct arity .product d,
    UniformNativeTractXWitness.output_correct arity .localAffine d,tensor_packets_correct arity d⟩

/-- Finite whole-programme primitive cost and storage at every execution prefix. -/
theorem source_resources (d : Data s arity) :
    primitiveCost (executes arity).machine ((executes arity).outputs d).steps
      (some (initList (executes arity).machine.computer
        (OriginalFamilyPackingMachine.encoding.encode (original arity d))))≤
      (executes arity).cost d*(executes arity).machine.primitiveBudget ∧
    ∀ j≤((executes arity).outputs d).steps, ∀ cfg : (executes arity).machine.Config,
      (fun p => p.bind (executes arity).machine.computer.step)^[j]
        (some (initList (executes arity).machine.computer
          (OriginalFamilyPackingMachine.encoding.encode (original arity d))))=some cfg →
      stackSize cfg.stk≤(OriginalFamilyPackingMachine.encoding.encode (original arity d)).length+
        (executes arity).cost d*(executes arity).machine.primitiveBudget := by
  let out := (executes arity).outputs d
  refine ⟨(primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ out.steps_le_m),?_⟩
  intro j hj cfg hcfg
  have hs := (executes arity).machine.run_size_le _ cfg j hcfg
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (hj.trans out.steps_le_m)) _)

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformNativeTractXDecision
