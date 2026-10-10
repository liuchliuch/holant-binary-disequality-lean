import Holant.OneHot.StackProgram.Machine.Concrete
import Holant.OneHot.StackProgram.GraphCodeOccurrence
import Holant.OneHot.StackProgram.Machine.Cost
import Holant.OneHot.Computable.Evaluation.GraphTraceBounds

/-! Actual fixed-field evaluation of graph-generated serialized bytecode.
The field, finite coefficient family, label alphabet and all rational constants
are fixed before the input graph. This module bounds the genuine bytecode
interpreter in the original graph's bit length. It does not implement or assume
a unit-cost graph-to-bytecode operation, and does not claim a raw-graph FP result. -/
namespace Holant.Complexity.FixedFieldMachines.StackEvaluatorBridge
open Turing Computability Holant.Algebraic Holant.OneHot Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.Machine
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.Complexity.ExactSignatureTables
open scoped BigOperators

/-- All stored literal, zero and unit words contribute to the fixed width constant. -/
def literalWidth {A V : Type} [Fintype A] [CommSemiring V]
    {e : Encoding V Bool} {coeff : A → V} (lits : Kernels.Literals e coeff) : ℕ :=
  (∑ a, (lits.table.words a).length) + lits.zeroWord.length + lits.oneWord.length

theorem literal_le {A V : Type} [Fintype A] [CommSemiring V]
    {e : Encoding V Bool} {coeff : A → V} (lits : Kernels.Literals e coeff) (a : A) :
    (e.encode (coeff a)).length ≤ literalWidth lits := by
  rw [← lits.table.correct a]
  have h := Finset.single_le_sum (f := fun a => (lits.table.words a).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  dsimp [literalWidth]
  omega

theorem zero_le {A V : Type} [Fintype A] [CommSemiring V]
    {e : Encoding V Bool} {coeff : A → V} (lits : Kernels.Literals e coeff) :
    (e.encode 0).length ≤ literalWidth lits := by rw [← lits.zero_correct]; unfold literalWidth; omega

theorem one_le {A V : Type} [Fintype A] [CommSemiring V]
    {e : Encoding V Bool} {coeff : A → V} (lits : Kernels.Literals e coeff) :
    (e.encode 1).length ≤ literalWidth lits := by rw [← lits.one_correct]; unfold literalWidth; omega

variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}

/-- A literal zero label is added without changing any original family coordinate. -/
def treeCoordinates (coeff : CoefficientIndex s b arity → Fin n → ℚ) :
    RawClosedNetwork.TreeLabel s b arity → Fin n → ℚ
  | none => 0
  | some a => coeff a

noncomputable def coefficients (F : FixedField K n) (coeff : CoefficientIndex s b arity → Fin n → ℚ) :=
  RawClosedNetwork.interpretLabel (fun a => F.decode (coeff a))

/-- Runtime words use only rational vectors and the fixed unitCode. The basis
and abstract field appear solely in erased codec-correctness proofs. -/
def literals (F : FixedField K n) (coeff : CoefficientIndex s b arity → Fin n → ℚ) :
    Kernels.Literals F.encoding (coefficients F coeff) where
  table.words a := (vectorEncoding n).encode (treeCoordinates coeff a)
  table.correct a := by
    cases a with
    | none =>
      simpa [treeCoordinates, coefficients, RawClosedNetwork.interpretLabel] using
        (F.encoding_decode (0 : Fin n → ℚ)).symm
    | some a => exact (F.encoding_decode (coeff a)).symm
  zeroWord := (vectorEncoding n).encode 0
  oneWord := (vectorEncoding n).encode F.unitCode
  zero_correct := by simpa using (F.encoding_decode (0 : Fin n → ℚ)).symm
  one_correct := by simpa using (F.encoding_decode F.unitCode).symm

/-- One fixed ordinary finite Boolean-stack interpreter, consuming bytecode. -/
noncomputable def machine (F : FixedField K n) (coeff : CoefficientIndex s b arity → Fin n → ℚ) :=
  fieldInterpreter F (treeLabelEncoding s b arity) (lengthBound s b arity)
    (coefficients F coeff) (literals F coeff)

noncomputable def width (F : FixedField K n) (coeff : CoefficientIndex s b arity → Fin n → ℚ) (L : ℕ) : ℕ :=
  ArithmeticSize.bitBound F (ArithmeticSize.withUnit F coeff) (5 * L) + literalWidth (literals F coeff)

def codeCount (L : ℕ) : ℕ := 55 * L + 1

noncomputable def runtimeBound (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ) (L : ℕ) : ℕ :=
  codeCount L * Interpreter.instructionBound (lengthBound s b arity) F.encoding
    (fieldProviders F) (width F coeff L) (codeCount L) + 6 * width F coeff L + 16

/-- The bit bound is an explicit fixed polynomial in the original graph length. -/
noncomputable def widthPolynomial (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ) : Polynomial ℕ :=
  let table := ArithmeticSize.withUnit F coeff
  let M := F.toArithmeticData.familyBound table
  let D := F.toArithmeticData.familyDenominator table
  Polynomial.C n * (4 * (5 * Polynomial.X + Polynomial.C M.size +
    (5 * Polynomial.X) * Polynomial.C (n * n * M * M).size +
    (2 * (5 * Polynomial.X) + 1) * Polynomial.C D.size + 3) + 1) +
    Polynomial.C (literalWidth (literals F coeff))

@[simp] theorem widthPolynomial_eval (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ) (L : ℕ) :
    (widthPolynomial F coeff).eval L = width F coeff L := by
  simp [widthPolynomial, width, ArithmeticSize.bitBound]

/-- The real scalar provider polynomials are composed with the proved width
polynomial; transfer/framing/dispatch costs and code count are included. -/
noncomputable def runtimePolynomial (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ) : Polynomial ℕ :=
  let W := widthPolynomial F coeff
  let H := 55 * Polynomial.X + 1
  let P := fieldProviders F
  let instruction := P.add.time.comp (3 * W + 1) + P.mul.time.comp (3 * W + 1) +
    14 * W + 18 + (2 * W + 4) * Polynomial.C (2 ^ 18) + 3 +
    Polynomial.C (2 * (lengthBound s b arity + 6)) + 4 * ((2 * W + 2) * H + 1) + 9
  H * instruction + 6 * W + 16

@[simp] theorem runtimePolynomial_eval (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ) (L : ℕ) :
    (runtimePolynomial F coeff).eval L = runtimeBound F coeff L := by
  simp [runtimePolynomial, runtimeBound, Interpreter.instructionBound, Kernels.timeBound, codeCount]

/-- Increasing only the stack-height allowance increases the real instruction
bound. The width and arithmetic-provider polynomials remain unchanged. -/
theorem instructionBound_mono_height {V : Type} [CommSemiring V]
    (C : ℕ) (e : Encoding V Bool) (P : Operator.Providers e) (W : ℕ)
    {H H' : ℕ} (h : H ≤ H') :
    Interpreter.instructionBound C e P W H ≤
      Interpreter.instructionBound C e P W H' := by
  unfold Interpreter.instructionBound
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (Nat.mul_le_mul_left _ h) 1)) _) 9

/-- The actual fixed interpreter returns the original field codec on the actual
graph-generated bytecode, with a polynomial bound in the original graph length.
One-hot and native-X assumptions constrain only occurrences in this graph. -/
theorem evaluate_graph_code (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (hf : ∀ v, Holant.Signature.OneHot
      (fun x => F.decode (coeff (.inl ⟨r.signatureLabel h v, x⟩))))
    (hX : ∀ e, (fun x y => F.decode (coeff (.inr (r.edgeLabel h e, x, y)))) =
      Holant.Signature.disequality) :
    ∃ time, time ≤ (runtimePolynomial F coeff).eval (RawClosedNetwork.encoding.encode r).length ∧
      Kernels.Executes (machine F coeff)
        ((codeEncoding (treeLabelEncoding s b arity)).encode (r.labelledGraphCode h))
        (F.encoding.encode ((r.realize h (fun i x => F.decode (coeff (.inl ⟨i, x⟩)))
          (fun i x y => F.decode (coeff (.inr (i, x, y))))).denote Fin.elim0)) time := by
  let L := (RawClosedNetwork.encoding.encode r).length
  let W := width F coeff L
  let c := r.labelledGraphCode h
  let N := r.executableRealize h (fun i x => F.decode (coeff (.inl ⟨i, x⟩)))
    (fun i x y => F.decode (coeff (.inr (i, x, y))))
  let p := N.computedOneHotProgram
  have hr : run (coefficients F coeff) c [] = some ([p.run.1], p.values) :=
    r.run_labelledGraphCode h (fun a => F.decode (coeff a)) []
  have hb := r.compiled_encoded_length_le F coeff h
    (fun i x => F.decode (coeff (.inl ⟨i, x⟩)))
    (fun i x y => F.decode (coeff (.inr (i, x, y))))
    (fun i x => ⟨.inl ⟨i, x⟩, rfl⟩)
  have hw : literalWidth (literals F coeff) ≤ W := Nat.le_add_left _ _
  have ht : ∀ x ∈ p.values, (F.encoding.encode x).length ≤ W := by
    intro x hx
    exact (hb.2 x hx).trans (Nat.le_add_right _ _)
  obtain ⟨time, htime, hexec⟩ := Interpreter.value_of_run
    (treeLabelEncoding s b arity) (lengthBound s b arity) F.encoding
    (coefficients F coeff) (literals F coeff) (fieldProviders F)
    (treeLabelEncoding_length_le s b arity) W
    (fun a => (literal_le (literals F coeff) a).trans hw)
    ((zero_le (literals F coeff)).trans hw) ((one_le (literals F coeff)).trans hw)
    c p.run.1 p.values hr ht
  have hc : c.length ≤ codeCount L := by
    have hc := r.labelledGraphCode_length_le_of_occurrences h
      (fun a => F.decode (coeff a)) hf hX
    have hl := r.counts_le_encoded_length
    dsimp [c, codeCount, L]
    omega
  have hm := instructionBound_mono_height (lengthBound s b arity) F.encoding (fieldProviders F) W hc
  have ht' : time ≤ runtimeBound F coeff L := htime.trans
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul hc hm) (6 * W)) 16)
  have hv := (N.computedOneHotProgram_spec hf hX).1
  change p.run.1 = N.denote Fin.elim0 at hv
  have hn : N = r.realize h (fun i x => F.decode (coeff (.inl ⟨i, x⟩)))
      (fun i x y => F.decode (coeff (.inr (i, x, y)))) := r.executableRealize_eq h _ _
  refine ⟨time, ?_, ?_⟩
  · simpa only [runtimePolynomial_eval] using ht'
  · change Kernels.Executes (machine F coeff) _ _ time at hexec
    rw [hv, hn] at hexec
    exact hexec

/-- A fixed multiplier accounts for every primitive instruction in the actual
finite interpreter syntax, including fixed literals and all scalar subroutines. -/
noncomputable def primitivePolynomial (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ) : Polynomial ℕ :=
  runtimePolynomial F coeff * Polynomial.C (machine F coeff).primitiveBudget

/-- The very same execution has both polynomial transition and primitive costs. -/
theorem evaluate_graph_code_with_primitive_cost (F : FixedField K n)
    (coeff : CoefficientIndex s b arity → Fin n → ℚ)
    (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (hf : ∀ v, Holant.Signature.OneHot
      (fun x => F.decode (coeff (.inl ⟨r.signatureLabel h v, x⟩))))
    (hX : ∀ e, (fun x y => F.decode (coeff (.inr (r.edgeLabel h e, x, y)))) =
      Holant.Signature.disequality) :
    ∃ time, time ≤ (runtimePolynomial F coeff).eval (RawClosedNetwork.encoding.encode r).length ∧
      Kernels.Executes (machine F coeff)
        ((codeEncoding (treeLabelEncoding s b arity)).encode (r.labelledGraphCode h))
        (F.encoding.encode ((r.realize h (fun i x => F.decode (coeff (.inl ⟨i, x⟩)))
          (fun i x y => F.decode (coeff (.inr (i, x, y))))).denote Fin.elim0)) time ∧
      primitiveCost (machine F coeff) time
        (some (initList (machine F coeff).computer
          ((codeEncoding (treeLabelEncoding s b arity)).encode (r.labelledGraphCode h)))) ≤
        (primitivePolynomial F coeff).eval (RawClosedNetwork.encoding.encode r).length := by
  obtain ⟨time, ht, hr⟩ := evaluate_graph_code F coeff r h hf hX
  refine ⟨time, ht, hr, ?_⟩
  simpa only [primitivePolynomial, Polynomial.eval_mul, Polynomial.eval_C] using
    (primitiveCost_le (machine F coeff) time _).trans (Nat.mul_le_mul_right _ ht)

end Holant.Complexity.FixedFieldMachines.StackEvaluatorBridge
