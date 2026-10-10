import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionTable

/-! Physical raw graph and original root ID to the prepared traversal entry.
The complete original-ID row table and root reference are both produced by
actual machines; no table or tree is accepted as an additional input. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionEntry
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1500000
variable {s b : ℕ} {arity : ℕ → ℕ}
def value (a z : Bool) (x : ResidualContext.Query s b arity) : List Bool :=
  Traversal.preparedInput (ResidualActionTable.value a z x.1) (Traversal.reference x.2.val)
noncomputable def computes (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :
    Computes (ResidualContext.queryEncoding s b arity) Frame.wordEncoding (value a z) :=
  recode ((leftMapComputes UnaryBinary.unaryEncoding (ResidualActionTable.computes a z s b arity)).andThen
    (rightMapComputes (framedListEncoding Frame.wordEncoding) ActionChild.referenceComputes))
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
abbrev machine (a z : Bool) (s b : ℕ) (arity : ℕ → ℕ) :=
  (LeftMap.machine (ResidualActionTable.machine a z s b arity)).compose (rightMapMachine ActionChild.referenceMachine)
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

noncomputable def sizePolynomial (s b : ℕ) (arity : ℕ → ℕ) : Polynomial ℕ :=
  let C := Polynomial.C (lengthBound s b arity)
  2*(Polynomial.X*(2*(8*C+6+Polynomial.X*(4*C+Polynomial.X+6))+2)+1)+Polynomial.X+3
theorem output_length (a z : Bool) (x : ResidualContext.Query s b arity) :
    (value a z x).length≤(sizePolynomial s b arity).eval (RawClosedNetwork.encoding.encode (ResidualContext.source x.1).val).length := by
  have ht := ResidualActionTable.output_length a z x.1
  have hv := x.2.isLt
  have hc := (ResidualContext.source x.1).val.counts_le_encoded_length
  change (Holant.Algebraic.frame (Traversal.tableBits (ResidualActionTable.value a z x.1))++Traversal.reference x.2.val).length≤_
  simp only [List.length_append,Holant.Algebraic.frame_length,Traversal.reference_length]
  simp only [sizePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
  dsimp only at ht
  omega
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualActionEntry
