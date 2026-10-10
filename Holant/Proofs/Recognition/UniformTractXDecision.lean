import Holant.Proofs.Recognition.UniformTensorDecision
import Holant.Proofs.Recognition.UniformTractXWitness
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionAny

/-!
# Physical decision of the exact four-clause TractX predicate

A single programme on the original-family RootCode word emits the exact TractX
Boolean and a retained witness bundle. The bundle contains the computed tensor
answer and the actual A/P/L encoded witness outputs (or negative `none`s).
Each of the three searches runs once; the final decision reads their real option
tags. All four source alternatives, mandatory equality-edge constraints, and
zero/nullary preprocessing are covered in both directions.

This is a halting original-descriptor decision for a fixed original arity layout,
not a polynomial recognition bound, not solver-code generation, and not the
seven-clause Tract criterion or a hardness conclusion on negative TractX inputs.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTractXDecision

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
open UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} (arity : Fin s → ℕ)

abbrev Witness := Option WitnessOutput.Output
abbrev Bundle := Bool × (Witness × (Witness × Witness))
abbrev witnessEncoding := WitnessOutput.resultEncoding
abbrev witnessPairEncoding := pairEncoding witnessEncoding witnessEncoding
abbrev witnessTripleEncoding := pairEncoding witnessEncoding witnessPairEncoding
abbrev bundleEncoding := pairEncoding encodingBoolBool witnessTripleEncoding

/-- All witness payloads come directly from their original raw system executions. -/
def bundle (d : Data s arity) : Bundle :=
  (UniformTensorDecision.arityFamily arity d,
    UniformTractXWitness.output arity .affine d,
    UniformTractXWitness.output arity .product d,
    UniformTractXWitness.output arity .localAffine d)

def witnessRuns (kind : UniformTractXWitness.Kind) :
    Runs OriginalFamilyPackingMachine.encoding witnessEncoding (original arity)
      (UniformTractXWitness.output arity kind) where
  machine := UniformTractXWitness.machine kind
  cost d := Classical.choose (UniformTractXWitness.outputs arity kind d)
  outputs d := Classical.choice (Classical.choose_spec (UniformTractXWitness.outputs arity kind d))

def bundleRuns : Runs OriginalFamilyPackingMachine.encoding bundleEncoding (original arity) (bundle arity) :=
  (UniformTensorDecision.arityFamilyRuns arity).pair
    ((witnessRuns arity .affine).pair ((witnessRuns arity .product).pair (witnessRuns arity .localAffine)))

/-- The source criterion is the disjunction of these four actual output tags. -/
def summary (b : Bundle) : Bool := b.1 || b.2.1.isSome || b.2.2.1.isSome || b.2.2.2.isSome

def presence : Computes witnessEncoding encodingBoolBool Option.isSome :=
  congrComputes ((OptionMap.computes
    (constantComputes WitnessOutput.outputEncoding encodingBoolBool true)).andThen OptionAny.computes)
    (fun q => by cases q <;> rfl)

def summaryComputes : Computes bundleEncoding encodingBoolBool summary := by
  let t := Wiring.firstComputes encodingBoolBool witnessTripleEncoding
  let rest := Wiring.secondComputes encodingBoolBool witnessTripleEncoding
  let a := (rest.andThen (Wiring.firstComputes witnessEncoding witnessPairEncoding)).andThen presence
  let tail := rest.andThen (Wiring.secondComputes witnessEncoding witnessPairEncoding)
  let p := (tail.andThen (Wiring.firstComputes witnessEncoding witnessEncoding)).andThen presence
  let l := (tail.andThen (Wiring.secondComputes witnessEncoding witnessEncoding)).andThen presence
  let op := Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.boolPairComputes (fun b => b.1 || b.2)
  exact ((pairComputes ((pairComputes ((pairComputes t a).andThen op) p).andThen op) l).andThen op)

def answer (d : Data s arity) : Bool := summary (bundle arity d)
def answerRuns : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity) (answer arity) :=
  (bundleRuns arity).after summaryComputes

/-- Exact source criterion, with the mandatory transformed equality edge in A/P/L. -/
theorem answer_correct (d : Data s arity) :
    answer arity d = true ↔ TractX (AffineBranch.indexedFamily d.G) := by
  rw [UniformTractXSemantics.tractX_iff_core]
  simp only [answer,summary,bundle,Bool.or_eq_true,UniformTensorDecision.arityAlternative_correct,
    UniformTractXWitness.output_correct,UniformTractXWitness.target,TractXCore,or_assoc]
  rfl

theorem answer_false_iff (d : Data s arity) :
    answer arity d = false ↔ ¬ TractX (AffineBranch.indexedFamily d.G) := by
  have hb : ∀ b : Bool, b = false ↔ ¬ b = true := by intro b; cases b <;> simp
  rw [hb,answer_correct]

/-- Retain the original witness bundle while computing its classification tag. -/
abbrev outputEncoding := pairEncoding encodingBoolBool bundleEncoding
def output (d : Data s arity) : Bool × Bundle := (answer arity d,bundle arity d)
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding (original arity) (output arity) :=
  (bundleRuns arity).after (pairComputes summaryComputes (identityComputes bundleEncoding))

/-- One complete physical run emits the source TractX answer and the actual
encoded A/P/L witnesses. No basis, field, accepted template, semantic evaluator,
or successful search height is part of its input. -/
theorem source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (executes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (outputEncoding.encode (output arity d))) ((executes arity).cost d)) ∧
    ((output arity d).1 = true ↔ TractX (AffineBranch.indexedFamily d.G)) ∧
    ((output arity d).1 = false ↔ ¬ TractX (AffineBranch.indexedFamily d.G)) ∧
    (((output arity d).2.2.1).isSome = true ↔
      CommonTransformable affineClass (AffineBranch.indexedFamily d.G)) ∧
    (((output arity d).2.2.2.1).isSome = true ↔
      CommonTransformable productClass (AffineBranch.indexedFamily d.G)) ∧
    (((output arity d).2.2.2.2).isSome = true ↔
      CommonTransformable localAffineClass (AffineBranch.indexedFamily d.G)) :=
  ⟨⟨(executes arity).outputs d⟩,answer_correct arity d,answer_false_iff arity d,
    UniformTractXWitness.output_correct arity .affine d,
    UniformTractXWitness.output_correct arity .product d,
    UniformTractXWitness.output_correct arity .localAffine d⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTractXDecision
