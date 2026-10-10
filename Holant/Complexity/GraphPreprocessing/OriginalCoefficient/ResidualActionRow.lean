import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionChildList
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionHeader
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin

/-! One complete original-ID traversal row directly from raw network bytes.
The actual header, canonical increasing children, flipped original parent-port
labels, original child references and terminal forest literal are all emitted
by finite Boolean-stack machines. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionRow
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1500000
variable {s b : ℕ} {arity : ℕ → ℕ}

def children (a z : Bool) (x : ResidualContext.Query s b arity) : List Bool :=
  ResidualActionChildList.value a z (ResidualActionChildList.original x)++Traversal.literals [false]
noncomputable def childrenComputes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (children a z) :=
  (pairComputes (ResidualActionChildList.originalComputes a z s b arity)
    (constantComputes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (Traversal.literals [false]))).andThen WordJoin.computes
def value (a z : Bool) (x : ResidualContext.Query s b arity) : List Bool :=
  ResidualActionHeader.value a z x++children a z x
noncomputable def computes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (value a z) :=
  (pairComputes (ResidualActionHeader.computes a z s b arity) (childrenComputes a z s b arity)).andThen WordJoin.computes
abbrev headerMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) := ResidualActionHeader.machine a z s b arity
abbrev childrenMachine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (ResidualActionChildList.originalMachine a z s b arity) (Constant.machine (Traversal.literals [false]))).compose WordJoin.machine
abbrev machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  (pairMachine (headerMachine a z s b arity) (childrenMachine a z s b arity)).compose WordJoin.machine
@[simp] theorem computes_machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : (computes a z s b arity).machine=machine a z s b arity := rfl
theorem inFP (a z : Bool) : InFP (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (value a z) := (computes a z s b arity).inFP

noncomputable def timePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  (computes a z s b arity).time.comp (7*(Polynomial.X+1))
noncomputable def timed (a z : Bool) (x : ResidualContext.Query s b arity) :
    TM2OutputsInTime (machine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x)
      (some (value a z x)) ((timePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length) where
  steps := ((computes a z s b arity).outputs x).steps
  evals_in_steps := ((computes a z s b arity).outputs x).evals_in_steps
  steps_le_m := by
    have h := natPolynomial_eval_mono (computes a z s b arity).time (ResidualContext.query_length x)
    exact le_trans ((computes a z s b arity).outputs x).steps_le_m (by simpa [timePolynomial] using h)
noncomputable def primitivePolynomial (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  timePolynomial a z s b arity*Polynomial.C (machine a z s b arity).primitiveBudget
theorem primitive_bound (a z : Bool) (x : ResidualContext.Query s b arity) :
    primitiveCost (machine a z s b arity) (timed a z x).steps
      (some (initList (machine a z s b arity).computer ((ResidualContext.queryEncoding s b arity).encode x))) ≤
      (primitivePolynomial a z s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length := by
  have h := Nat.mul_le_mul_right (machine a z s b arity).primitiveBudget (timed a z x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h
theorem output_length (a z : Bool) (x : ResidualContext.Query s b arity) :
    (value a z x).length≤8*lengthBound s b arity+6+(RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length*
      (4*lengthBound s b arity+(RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length+6) := by
  have hh := ResidualActionHeader.output_length a z x
  have hc := ResidualActionChildList.output_length a z x
  simp only [value,children,List.length_append,Traversal.literals_length,List.length_cons,List.length_nil]
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionRow
