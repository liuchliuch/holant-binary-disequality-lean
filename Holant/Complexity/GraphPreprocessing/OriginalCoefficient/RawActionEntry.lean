import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionTable

/-! Physical raw graph and original root ID to the prepared traversal entry.
The complete original-ID row table and root reference are both produced by
actual machines; no table or tree is accepted as an additional input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionEntry
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}
def value (x : RawRootReach.Input s b arity) : List Bool :=
  Traversal.preparedInput (RawActionTable.value x.1) (Traversal.reference x.2.val)
noncomputable def computes (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding value :=
  recode ((leftMapComputes UnaryBinary.unaryEncoding (RawActionTable.computes s b arity)).andThen
    (rightMapComputes (framedListEncoding Frame.wordEncoding) ActionChild.referenceComputes))
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
abbrev machine (s b : ℕ) (arity : ℕ → ℕ) :=
  (LeftMap.machine (RawActionTable.machine s b arity)).compose (rightMapMachine ActionChild.referenceMachine)
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

noncomputable def sizePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  let C := Polynomial.C (lengthBound s b arity)
  2*(Polynomial.X*(2*(8*C+6+Polynomial.X*(4*C+Polynomial.X+6))+2)+1)+Polynomial.X+3
theorem output_length (x : RawRootReach.Input s b arity) :
    (value x).length≤(sizePolynomial s b arity).eval (RawClosedNetwork.encoding.encode x.1.val).length := by
  have ht := RawActionTable.output_length x.1
  have hv := x.2.isLt
  have hc := x.1.val.counts_le_encoded_length
  change (Holant.Algebraic.frame (Traversal.tableBits (RawActionTable.value x.1))++Traversal.reference x.2.val).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,Traversal.reference_length]
  simp only [sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  dsimp only at ht
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RawActionEntry
