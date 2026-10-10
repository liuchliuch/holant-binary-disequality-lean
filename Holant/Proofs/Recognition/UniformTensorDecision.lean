import Holant.Proofs.Recognition.UniformTensorDecisionRuns

/-!
# Complete physical original-descriptor decisions for source tensor alternatives

One programme per fixed original arity family receives the original packed
RootCode word and emits BOTH unary/binary tensor membership and matching tensor
membership. Matching uses one common orientation outside the family universal.
Finite physical all/any folds run the literal polynomial branch machines; no
semantic predicate decider, field selection, factorization, evaluator, transformed
descriptor, or successful search height is supplied at runtime. This is a
halting decision result on legal represented inputs, not a polynomial-time bound
for structural recognition and not yet the full seven-clause decision theorem.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecision

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
open UniformTensorDecisionBranch TensorDecisionCleared
noncomputable section

variable {s : ℕ} (arity : Fin s → ℕ)

/-- Finite ordered shape catalogues depend only on original port counts. -/
def arityShapes (n : ℕ) : List (TensorDecision.Shape n) := Finset.univ.toList
def matchingShapes (n : ℕ) : List (TensorDecisionStable.Shape n) := Finset.univ.toList

@[simp] theorem mem_arityShapes {n : ℕ} (S : TensorDecision.Shape n) : S ∈ arityShapes n := by
  simp [arityShapes]
@[simp] theorem mem_matchingShapes {n : ℕ} (S : TensorDecisionStable.Shape n) :
    S ∈ matchingShapes n := by simp [matchingShapes]

def allZero (mode : Option Bool) (i : Fin s) (d : Data s arity) : Bool :=
  (SparseTransform.allWords (arity i)).all (fun x => ground arity (table arity mode i x) d)

def allZeroRuns (mode : Option Bool) (i : Fin s) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (allZero arity mode i) :=
  Runs.all (fun d x => ground arity (table arity mode i x) d)
    (fun x => groundRuns arity (table arity mode i x)) (SparseTransform.allWords (arity i))

theorem allZero_correct (mode : Option Bool) (i : Fin s) (d : Data s arity) :
    allZero arity mode i d = true ↔ ∀ x, signature arity mode d i x = 0 := by
  simp only [allZero,List.all_eq_true,SparseTransform.mem_allWords,forall_true_left,
    ground_correct,table_eval]

def arityBranch (i : Fin s) (S : TensorDecision.Shape (arity i))
    (pivot : Fin (arity i) → Bool) (d : Data s arity) : Bool :=
  branchAnswer arity false (table arity none i) S.count S.arity S.ports pivot d

def arityBranchRuns (i : Fin s) (S : TensorDecision.Shape (arity i))
    (pivot : Fin (arity i) → Bool) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (arityBranch arity i S pivot) :=
  branchRuns arity false (table arity none i) S.count S.arity S.ports pivot

theorem arityBranch_correct (i : Fin s) (S : TensorDecision.Shape (arity i))
    (pivot : Fin (arity i) → Bool) (d : Data s arity) :
    arityBranch arity i S pivot d = true ↔ ArityTwoAccepts (d.G i) S pivot := by
  rw [arityBranch,branch_correct]
  simp_rw [table_eval]
  exact UniformTensorDecisionSyntax.arityTwo_branch_iff _ _ _

def arityLabel (i : Fin s) (d : Data s arity) : Bool :=
  allZero arity none i d || (arityShapes (arity i)).any (fun S =>
    (SparseTransform.allWords (arity i)).any (fun p => arityBranch arity i S p d))

def arityLabelRuns (i : Fin s) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity) (arityLabel arity i) :=
  Runs.bool Bool.or (allZeroRuns arity none i)
    (Runs.any (fun d S => (SparseTransform.allWords (arity i)).any (fun p => arityBranch arity i S p d))
      (fun S => Runs.any (fun d p => arityBranch arity i S p d)
        (fun p => arityBranchRuns arity i S p) (SparseTransform.allWords (arity i)))
      (arityShapes (arity i)))

theorem arityLabel_correct (i : Fin s) (d : Data s arity) :
    arityLabel arity i d = true ↔ SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) (d.G i) := by
  rw [arityTwo_source_iff]
  simp only [arityLabel,Bool.or_eq_true,allZero_correct,List.any_eq_true,
    mem_arityShapes,SparseTransform.mem_allWords,true_and,arityBranch_correct,
    ArityTwoTest,signature]

def matchingBranch (opposite : Bool) (i : Fin s) (S : TensorDecisionStable.Shape (arity i))
    (pivot : Fin (arity i) → Bool) (d : Data s arity) : Bool :=
  branchAnswer arity true (table arity (some opposite) i) S.count S.arity S.ports pivot d

def matchingBranchRuns (opposite : Bool) (i : Fin s) (S : TensorDecisionStable.Shape (arity i))
    (pivot : Fin (arity i) → Bool) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (matchingBranch arity opposite i S pivot) :=
  branchRuns arity true (table arity (some opposite) i) S.count S.arity S.ports pivot

theorem matchingBranch_correct (opposite : Bool) (i : Fin s)
    (S : TensorDecisionStable.Shape (arity i)) (pivot : Fin (arity i) → Bool) (d : Data s arity) :
    matchingBranch arity opposite i S pivot d = true ↔
      OneHotAccepts ((TensorDecisionMatching.basis opposite).symm.action (d.G i)) S pivot := by
  rw [matchingBranch,branch_correct]
  simp_rw [table_eval]
  exact UniformTensorDecisionSyntax.oneHot_branch_iff _ _ _

def matchingLabel (opposite : Bool) (i : Fin s) (d : Data s arity) : Bool :=
  allZero arity (some opposite) i d || (matchingShapes (arity i)).any (fun S =>
    (SparseTransform.allWords (arity i)).any (fun p => matchingBranch arity opposite i S p d))

def matchingLabelRuns (opposite : Bool) (i : Fin s) :
    Runs OriginalFamilyPackingMachine.encoding encodingBoolBool (original arity)
      (matchingLabel arity opposite i) :=
  Runs.bool Bool.or (allZeroRuns arity (some opposite) i)
    (Runs.any (fun d S => (SparseTransform.allWords (arity i)).any
      (fun p => matchingBranch arity opposite i S p d))
      (fun S => Runs.any (fun d p => matchingBranch arity opposite i S p d)
        (fun p => matchingBranchRuns arity opposite i S p) (SparseTransform.allWords (arity i)))
      (matchingShapes (arity i)))

theorem matchingLabel_correct (opposite : Bool) (i : Fin s) (d : Data s arity) :
    matchingLabel arity opposite i d = true ↔ SourceTensorClosure (matchingImage opposite) (d.G i) := by
  rw [matching_source_iff]
  simp only [matchingLabel,Bool.or_eq_true,allZero_correct,List.any_eq_true,
    mem_matchingShapes,SparseTransform.mem_allWords,true_and,matchingBranch_correct,
    OneHotTest,signature]

def arityFamily (d : Data s arity) : Bool := (List.finRange s).all (fun i => arityLabel arity i d)
def arityFamilyRuns : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (arityFamily arity) :=
  Runs.all (fun d i => arityLabel arity i d) (fun i => arityLabelRuns arity i) (List.finRange s)

theorem arityFamily_correct (d : Data s arity) :
    arityFamily arity d = true ↔ ∀ i, SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) (d.G i) := by
  simp only [arityFamily,List.all_eq_true,List.mem_finRange,forall_true_left,arityLabel_correct]

def orientation (opposite : Bool) (d : Data s arity) : Bool :=
  (List.finRange s).all (fun i => matchingLabel arity opposite i d)
def orientationRuns (opposite : Bool) : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (orientation arity opposite) :=
  Runs.all (fun d i => matchingLabel arity opposite i d)
    (fun i => matchingLabelRuns arity opposite i) (List.finRange s)

theorem orientation_correct (opposite : Bool) (d : Data s arity) :
    orientation arity opposite d = true ↔ ∀ i, SourceTensorClosure (matchingImage opposite) (d.G i) := by
  simp only [orientation,List.all_eq_true,List.mem_finRange,forall_true_left,matchingLabel_correct]

/-- One orientation is chosen for the whole family, as required by source clause (4). -/
def matchingFamily (d : Data s arity) : Bool := orientation arity false d || orientation arity true d

def matchingFamilyRuns : Runs OriginalFamilyPackingMachine.encoding encodingBoolBool
    (original arity) (matchingFamily arity) :=
  Runs.bool Bool.or (orientationRuns arity false) (orientationRuns arity true)

theorem matchingFamily_correct (d : Data s arity) :
    matchingFamily arity d = true ↔
      (∀ i, SourceTensorClosure (matchingImage false) (d.G i)) ∨
      (∀ i, SourceTensorClosure (matchingImage true) (d.G i)) := by
  simp only [matchingFamily,Bool.or_eq_true,orientation_correct]

/-- The exact original signature family, retaining arbitrary arities and coefficients. -/
def family (d : Data s arity) : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin s => (⟨arity i,d.G i⟩ : AnySignature AlgebraicComplex))

theorem arityAlternative_correct (d : Data s arity) :
    arityFamily arity d = true ↔ ArityTwoAlternative (family arity d) := by
  rw [arityFamily_correct]
  simp only [ArityTwoAlternative,family,Set.forall_mem_range]

theorem matchingAlternative_correct (d : Data s arity) :
    matchingFamily arity d = true ↔ MatchingAlternative (family arity d) := by
  rw [matchingFamily_correct]
  simp only [MatchingAlternative,family,Set.forall_mem_range]

abbrev outputEncoding := pairEncoding encodingBoolBool encodingBoolBool
def output (d : Data s arity) : Bool × Bool := (arityFamily arity d,matchingFamily arity d)
def executes : Runs OriginalFamilyPackingMachine.encoding outputEncoding (original arity) (output arity) :=
  (arityFamilyRuns arity).pair (matchingFamilyRuns arity)

/-- A physical terminating programme on the original represented family word,
with exact positive and negative answers for both source tensor alternatives. -/
theorem source (d : Data s arity) :
    Nonempty (TM2OutputsInTime (executes arity).machine.computer
      (OriginalFamilyPackingMachine.encoding.encode (original arity d))
      (some (outputEncoding.encode (output arity d))) ((executes arity).cost d)) ∧
    ((output arity d).1 = true ↔ ∀ i, SourceTensorClosure (fun m _ => m = 1 ∨ m = 2) (d.G i)) ∧
    ((output arity d).2 = true ↔
      (∀ i, SourceTensorClosure (matchingImage false) (d.G i)) ∨
      (∀ i, SourceTensorClosure (matchingImage true) (d.G i))) :=
  ⟨⟨(executes arity).outputs d⟩,arityFamily_correct arity d,matchingFamily_correct arity d⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTensorDecision
