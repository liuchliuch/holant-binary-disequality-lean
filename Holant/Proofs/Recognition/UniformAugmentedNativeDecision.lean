import Holant.Proofs.Recognition.UniformNativeTractXDecision

/-!
# Literal equality augmentation of the original native criterion

The physical frontend prepends the prescribed equality tensor, with generated
rational RootCodes, before executing native four-clause recognition. The input
contains only the original family's descriptors. The result decides exactly
TractX(K (G union {I})), retaining all actual native search packets. Arity layout
is fixed programme syntax; this is not a varying-layout compiler.
-/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformAugmentedNativeDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open PhysicalFolds UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {s : ℕ} (arity : Fin s → ℕ)

abbrev augmentedArity : Fin (s+1) → ℕ := Fin.cases 2 arity

def equalityCode (x : Fin 2 → Bool) : RootCode :=
  RationalRootCode.code (OriginalFamilyInput.edgeValue false (x 0) (x 1))

theorem equalityCode_represents (x : Fin 2 → Bool) :
    (equalityCode x).Represents ((Signature.equality (x 0) (x 1) : AlgebraicComplex) : ℂ) := by
  have h := RationalRootCode.represents (OriginalFamilyInput.edgeValue false (x 0) (x 1))
  have hc := OriginalFamilyInput.edgeValue_coe false (x 0) (x 1)
  change ((OriginalFamilyInput.edgeValue false (x 0) (x 1) : ℚ) : AlgebraicComplex)=Signature.equality (x 0) (x 1) at hc
  simpa [equalityCode,←hc] using h

def augmentedInput (d : Data s arity) : OriginalFamilyInput.Input (augmentedArity arity) :=
  Fin.cases equalityCode d.input

def augmentedValues (d : Data s arity) :
    (i : Fin (s+1)) → Signature AlgebraicComplex (augmentedArity arity i) :=
  Fin.cases (fun x : Fin 2 → Bool => Signature.equality (x 0) (x 1)) d.G

def augment (d : Data s arity) : Data (s+1) (augmentedArity arity) where
  input := augmentedInput arity d
  G := augmentedValues arity d
  represented i := by
    induction i using Fin.cases with
    | zero => exact equalityCode_represents
    | succ i => exact d.represented i

abbrev equalitySignature : AnySignature AlgebraicComplex := ⟨2,fun x => Signature.equality (x 0) (x 1)⟩

theorem augmented_family (d : Data s arity) :
    AffineBranch.indexedFamily (augment arity d).G =
      AffineBranch.indexedFamily d.G ∪ {equalitySignature} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    induction i using Fin.cases with
    | zero => exact Or.inr rfl
    | succ i => exact Or.inl ⟨i,rfl⟩
  · rintro (⟨i,rfl⟩ | h)
    · exact ⟨i.succ,rfl⟩
    · exact ⟨0,h.symm⟩

def equalityVertex : OriginalFamilyPackingMachine.Vertex :=
  (2,(SparseTransform.allWords 2).map equalityCode)

def prepend (r : OriginalFamilyPackingMachine.Input) : OriginalFamilyPackingMachine.Input :=
  (equalityVertex::r.1,r.2)

def prependComputes : Computes OriginalFamilyPackingMachine.encoding
    OriginalFamilyPackingMachine.encoding prepend :=
  pairComputes
    ((pairComputes (constantComputes OriginalFamilyPackingMachine.encoding
      OriginalFamilyPackingMachine.vertexEncoding equalityVertex) OriginalFamilyPackingMachine.family).andThen
        (StructuralListMachine.consComputes OriginalFamilyPackingMachine.vertexEncoding))
    OriginalFamilyPackingMachine.edgeFlag

theorem prepend_original (d : Data s arity) :
    prepend (original arity d)=original (augmentedArity arity) (augment arity d) := by
  unfold original OriginalFamilyPackingSource.fromSource
  simp only [prepend,List.finRange_succ,List.map_cons,List.map_map]
  rfl

def augmentedRuns (d : Data s arity) := UniformNativeTractXDecision.output (augmentedArity arity) (augment arity d)

def executes : Runs OriginalFamilyPackingMachine.encoding UniformNativeTractXDecision.outputEncoding
    (original arity) (augmentedRuns arity) :=
  ((Runs.ofComputes prependComputes (original arity)).congr (prepend_original arity)).comp
    { machine := (UniformNativeTractXDecision.executes (augmentedArity arity)).machine
      cost d := (UniformNativeTractXDecision.executes (augmentedArity arity)).cost (augment arity d)
      outputs d := (UniformNativeTractXDecision.executes (augmentedArity arity)).outputs (augment arity d) }

def answer (d : Data s arity) := (augmentedRuns arity d).1

theorem answer_correct (d : Data s arity) :
    answer arity d=true ↔ TractX (familyAction sourceKBasis
      (AffineBranch.indexedFamily d.G ∪ {equalitySignature})) := by
  change UniformNativeTractXDecision.answer (augmentedArity arity) (augment arity d)=true ↔ _
  rw [UniformNativeTractXDecision.answer_correct,augmented_family]

theorem answer_false_iff (d : Data s arity) :
    answer arity d=false ↔ ¬TractX (familyAction sourceKBasis
      (AffineBranch.indexedFamily d.G ∪ {equalitySignature})) := by
  have hb : ∀b : Bool,b=false ↔ ¬b=true := by intro b; cases b <;> simp
  rw [hb,answer_correct]

theorem source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (executes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (UniformNativeTractXDecision.outputEncoding.encode (augmentedRuns arity d)))
      ((executes arity).cost d)) ∧
    (answer arity d=true ↔ TractX (familyAction sourceKBasis
      (AffineBranch.indexedFamily d.G ∪ {equalitySignature}))) ∧
    (answer arity d=false ↔ ¬TractX (familyAction sourceKBasis
      (AffineBranch.indexedFamily d.G ∪ {equalitySignature}))) :=
  ⟨⟨(executes arity).outputs d⟩,answer_correct arity d,answer_false_iff arity d⟩

theorem source_resources (d : Data s arity) :
    primitiveCost (executes arity).machine ((executes arity).outputs d).steps
      (some (initList (executes arity).machine.computer
        (OriginalFamilyPackingMachine.encoding.encode (original arity d))))≤
        (executes arity).cost d*(executes arity).machine.primitiveBudget ∧
    ∀ j, j≤((executes arity).outputs d).steps → ∀ cfg : (executes arity).machine.Config,
      (fun z => z.bind (executes arity).machine.computer.step)^[j]
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
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformAugmentedNativeDecision
