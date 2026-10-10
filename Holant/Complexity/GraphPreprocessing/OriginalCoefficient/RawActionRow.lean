import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChildList
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionHeaderBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin

/-! One complete original-ID traversal row directly from raw network bytes.
The actual header, canonical increasing children, flipped original parent-port
labels, original child references and terminal forest literal are all emitted
by finite Boolean-stack machines. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionRow
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

def children (x : RawRootReach.Input s b arity) : List Bool :=
  ActionChildList.value (ActionChildList.original x)++Traversal.literals [false]
noncomputable def childrenComputes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding children :=
  (pairComputes (ActionChildList.originalComputes s b arity)
    (constantComputes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding (Traversal.literals [false]))).andThen WordJoin.computes
def value (x : RawRootReach.Input s b arity) : List Bool :=
  ActionHeader.value (ParentCoefficient.originalInput x)++children x
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding value :=
  (pairComputes (ActionHeader.originalComputes s b arity) (childrenComputes s b arity)).andThen WordJoin.computes
abbrev headerMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine identityMachine RawParentRow.machine).compose (ActionHeader.machine s b arity)
abbrev childrenMachine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (ActionChildList.originalMachine s b arity) (Constant.machine (Traversal.literals [false]))).compose WordJoin.machine
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (headerMachine s b arity) (childrenMachine s b arity)).compose WordJoin.machine
@[simp] theorem computes_machine (s b : ℕ) (arity : ℕ → ℕ) : (computes s b arity).machine=machine s b arity := rfl
theorem inFP : InFP (RawRootReach.inputEncoding s b arity) Frame.wordEncoding value := (computes s b arity).inFP

noncomputable def timePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes s b arity).time.comp (3*(Polynomial.X+1))
noncomputable def timed (x : RawRootReach.Input s b arity) :
    TM2OutputsInTime (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x)
      (some (value x)) ((timePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length) where
  steps := ((computes s b arity).outputs x).steps
  evals_in_steps := ((computes s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (computes s b arity).time (RawRootReach.input_length_le_original x)
    exact le_trans ((computes s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial s b arity*Polynomial.C (machine s b arity).primitiveBudget
theorem primitive_bound (x : RawRootReach.Input s b arity) :
    primitiveCost (machine s b arity) (timed x).steps
      (some (initList (machine s b arity).computer ((RawRootReach.inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have h := Nat.mul_le_mul_right (machine s b arity).primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
theorem output_length (x : RawRootReach.Input s b arity) :
    (value x).length≤8*lengthBound s b arity+6+(RawClosedNetwork.encoding.encode x.1.val).length*
      (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode x.1.val).length+6) := by
  have hh := ActionHeader.output_length (ParentCoefficient.originalInput x)
  have hc := ActionChildList.output_length x
  simp only [value,children,List.length_append,Traversal.literals_length,List.length_cons,List.length_nil]
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionRow
