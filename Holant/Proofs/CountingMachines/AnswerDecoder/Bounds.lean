import Holant.Proofs.CountingMachines.AnswerDecoder.Machine

/-! Resource bounds for every genuine encoded field input.  Polynomial time is
obtained from the implemented scalar machines and composition, not from answer
length.  All tape symbols, including parsing and arithmetic scratch, are counted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines StackProtocol

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

/-- The actual elementary instructions of the finite decoder. -/
theorem primitive_bound (F : FixedField K n) (y : K) :
    primitiveCost (computes F).machine ((computes F).outputs y).steps
      (some (initList (computes F).machine.computer (F.encoding.encode y))) ≤
      (primitivePolynomial (computes F)).eval (F.encoding.encode y).length :=
  computes_primitive_cost (computes F) y

def scratchPolynomial (F : FixedField K n) : Polynomial ℕ :=
  Polynomial.X + primitivePolynomial (computes F)

/-- Every reached prefix is covered, rather than only the final clean output. -/
theorem scratch_bound (F : FixedField K n) (y : K) (t : ℕ)
    (ht : t ≤ ((computes F).outputs y).steps) (d : (computes F).machine.Config)
    (hrun : (fun q => q.bind (computes F).machine.computer.step)^[t]
      (some (initList (computes F).machine.computer (F.encoding.encode y))) = some d) :
    stackSize d.stk ≤ (scratchPolynomial F).eval (F.encoding.encode y).length := by
  have h := (computes F).machine.run_size_le _ d t hrun
  rw [Machine.size_init] at h
  have ht' := ht.trans ((computes F).outputs y).steps_le_m
  have hm := Nat.mul_le_mul_right (computes F).machine.primitiveBudget ht'
  simp only [scratchPolynomial, primitivePolynomial, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  omega

/-- The answer itself is produced by transitions; no output bound is assumed. -/
theorem recovery_output_length (F : FixedField K n) (y : K) :
    (encodingNatBool.encode (natural F y)).length ≤
      (computes F).outputBound.bound.eval (F.encoding.encode y).length :=
  (computes F).outputBound.length_le y

/-- A separate physical scalar writer supplies a bit-length bound for cast
answers whenever a reduction starts from a natural counting-size theorem. -/
def castAnswerBound (F : FixedField K n) :
    PolynomialOutputBound encodingNatBool F.encoding (fun m : ℕ => (m : K)) :=
  (natCastComputes F).outputBound

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder
