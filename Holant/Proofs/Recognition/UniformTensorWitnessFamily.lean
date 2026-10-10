import Holant.Proofs.Recognition.UniformTensorWitness

/-!
# Original-family tensor certificates and a shared matching orientation

The companion physical output contains a zero flag or a complete shape/port/pivot
packet with actual algebraic witness for every original label. Matching selects
one orientation for the whole family before exposing its certificate list.
The run preserves all source labels in their original order.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorWitnessFamily

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open PhysicalFolds UniformTensorDecisionBranch UniformTensorWitness
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Physical list assembly, with every actual returned payload retained. -/
def collectRuns {D A B C : Type} {ea : Encoding A Bool} (eb : Encoding B Bool)
    {input : D → A} (f : C → D → B) (w : ∀ c, Runs ea eb input (f c)) :
    (cs : List C) → Runs ea (framedListEncoding eb) input (fun d => cs.map (fun c => f c d))
  | [] => Runs.constant ea (framedListEncoding eb) input []
  | c::cs => (w c |>.pair (collectRuns eb f w cs)).after (StructuralListMachine.consComputes eb)

abbrev familyEncoding := framedListEncoding labelEncoding
variable {s : ℕ} (arity : Fin s → ℕ)

def arityFamily (d : Data s arity) : List LabelCertificate :=
  (List.finRange s).map (fun i => arityLabel arity i d)
def arityFamilyRuns : Runs OriginalFamilyPackingMachine.encoding familyEncoding (original arity) (arityFamily arity) :=
  collectRuns labelEncoding (arityLabel arity) (arityLabelRuns arity) (List.finRange s)

theorem arityFamily_correct (d : Data s arity) :
    (∀ c ∈ arityFamily arity d, accepted c = true) ↔
      ArityTwoAlternative (UniformTensorDecision.family arity d) := by
  simp only [arityFamily,List.forall_mem_map,List.mem_finRange,forall_true_left,
    arityLabel_correct,ArityTwoAlternative,UniformTensorDecision.family,Set.forall_mem_range]

def matchingFamily (opposite : Bool) (d : Data s arity) : List LabelCertificate :=
  (List.finRange s).map (fun i => matchingLabel arity opposite i d)
def matchingFamilyRuns (opposite : Bool) : Runs OriginalFamilyPackingMachine.encoding familyEncoding
    (original arity) (matchingFamily arity opposite) :=
  collectRuns labelEncoding (matchingLabel arity opposite) (matchingLabelRuns arity opposite) (List.finRange s)

theorem matchingFamily_correct (opposite : Bool) (d : Data s arity) :
    (∀ c ∈ matchingFamily arity opposite d, accepted c = true) ↔
      ∀ i, SourceTensorClosure (matchingImage opposite) (d.G i) := by
  simp only [matchingFamily,List.forall_mem_map,List.mem_finRange,forall_true_left,matchingLabel_correct]

abbrev choiceEncoding := pairEncoding encodingBoolBool familyEncoding

def choice (d : Data s arity) : Bool × List LabelCertificate :=
  if UniformTensorDecision.orientation arity false d then (false,matchingFamily arity false d)
  else (true,matchingFamily arity true d)

def choiceRuns : Runs OriginalFamilyPackingMachine.encoding choiceEncoding (original arity) (choice arity) :=
  (UniformTensorDecision.orientationRuns arity false).choose
    ((Runs.constant _ _ (original arity) false).pair (matchingFamilyRuns arity false))
    ((Runs.constant _ _ (original arity) true).pair (matchingFamilyRuns arity true))

abbrev matchingEncoding := pairEncoding encodingBoolBool choiceEncoding

def matchingOutput (d : Data s arity) : Bool × (Bool × List LabelCertificate) :=
  (UniformTensorDecision.matchingFamily arity d,choice arity d)
def matchingRuns : Runs OriginalFamilyPackingMachine.encoding matchingEncoding (original arity) (matchingOutput arity) :=
  (UniformTensorDecision.matchingFamilyRuns arity).pair (choiceRuns arity)

theorem matching_correct (d : Data s arity) :
    (matchingOutput arity d).1 = true ↔ MatchingAlternative (UniformTensorDecision.family arity d) :=
  UniformTensorDecision.matchingAlternative_correct arity d

/-- Every matching label certificate uses the single orientation carried in the output. -/
theorem matching_selected (d : Data s arity) (h : (matchingOutput arity d).1 = true) :
    (∀ i, SourceTensorClosure (matchingImage (matchingOutput arity d).2.1) (d.G i)) ∧
      (∀ c ∈ (matchingOutput arity d).2.2, accepted c = true) := by
  have hh : UniformTensorDecision.orientation arity false d = true ∨
      UniformTensorDecision.orientation arity true d = true := by
    simpa only [matchingOutput,UniformTensorDecision.matchingFamily,Bool.or_eq_true] using h
  by_cases hf : UniformTensorDecision.orientation arity false d = true
  · have hc := (UniformTensorDecision.orientation_correct arity false d).mp hf
    simpa [matchingOutput,choice,hf] using
      (And.intro hc ((matchingFamily_correct arity false d).mpr hc))
  · have ht := hh.resolve_left hf
    have hc := (UniformTensorDecision.orientation_correct arity true d).mp ht
    simpa [matchingOutput,choice,hf] using
      (And.intro hc ((matchingFamily_correct arity true d).mpr hc))

abbrev outputEncoding := pairEncoding familyEncoding matchingEncoding

def output (d : Data s arity) := (arityFamily arity d,matchingOutput arity d)
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding (original arity) (output arity) :=
  (arityFamilyRuns arity).pair (matchingRuns arity)

/-- A complete physical companion emitter on the unchanged original descriptor word. -/
theorem source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (executes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (outputEncoding.encode (output arity d))) ((executes arity).cost d)) ∧
    ((∀ c ∈ (output arity d).1, accepted c = true) ↔
      ArityTwoAlternative (UniformTensorDecision.family arity d)) ∧
    ((output arity d).2.1 = true ↔ MatchingAlternative (UniformTensorDecision.family arity d)) ∧
    ((output arity d).2.1 = true →
      (∀ i, SourceTensorClosure (matchingImage (output arity d).2.2.1) (d.G i)) ∧
      (∀ c ∈ (output arity d).2.2.2, accepted c = true)) :=
  ⟨⟨(executes arity).outputs d⟩,arityFamily_correct arity d,matching_correct arity d,matching_selected arity d⟩

/-- Optional combined output retains the already verified exact four-clause
answer, A/P/L wires, and this entire ordered tensor-certificate bundle. -/
abbrev tractXOutputEncoding := pairEncoding UniformTractXDecision.outputEncoding outputEncoding
def tractXOutput (d : Data s arity) := (UniformTractXDecision.output arity d,output arity d)
def tractXExecutes : Runs OriginalFamilyPackingMachine.encoding tractXOutputEncoding (original arity) (tractXOutput arity) :=
  (UniformTractXDecision.executes arity).pair (executes arity)

theorem tractX_source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (tractXExecutes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (tractXOutputEncoding.encode (tractXOutput arity d))) ((tractXExecutes arity).cost d)) ∧
    ((tractXOutput arity d).1.1 = true ↔ TractX (AffineBranch.indexedFamily d.G)) :=
  ⟨⟨(tractXExecutes arity).outputs d⟩,UniformTractXDecision.answer_correct arity d⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorWitnessFamily
