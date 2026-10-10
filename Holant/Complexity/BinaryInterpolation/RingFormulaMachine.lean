import Holant.Complexity.BinaryInterpolation.RingFormula

/-! One actual finite interpreter evaluates arbitrarily large division-free
formulas over fixed algebraic constants, with polynomial bit-time in the
explicit formula size. The formula-to-bytes producer is a separate interface. -/
namespace Holant.Complexity.BinaryInterpolation.RingFormulaMachine
open Turing Computability Holant.Algebraic Holant.OneHot Holant.OneHot.StackProgram
open Holant.OneHot.StackProgram.Machine
open scoped BigOperators
noncomputable section
variable {A K : Type} [Fintype A] [DecidableEq A] [Field K] [Algebra ℚ K] {n : ℕ}

def coefficients (F : FixedField K n) (coeff : A→Fin n→ℚ) : A→K := fun a => F.decode (coeff a)

def literals (F : FixedField K n) (coeff : A→Fin n→ℚ) :
    Kernels.Literals F.encoding (coefficients F coeff) where
  table.words a := (vectorEncoding n).encode (coeff a)
  table.correct a := (F.encoding_decode (coeff a)).symm
  zeroWord := (vectorEncoding n).encode 0
  oneWord := (vectorEncoding n).encode F.unitCode
  zero_correct := by simpa using (F.encoding_decode (0 : Fin n→ℚ)).symm
  one_correct := by simpa using (F.encoding_decode F.unitCode).symm

def labelBound (labels : Encoding A Bool) : ℕ := ∑a,(labels.encode a).length

theorem label_le (labels : Encoding A Bool) (a : A) :
    (labels.encode a).length≤labelBound labels :=
  Finset.single_le_sum (f := fun x => (labels.encode x).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

def widthPolynomial (F : FixedField K n) (coeff : A→Fin n→ℚ) : Polynomial ℕ :=
  let M := F.toArithmeticData.familyBound coeff
  let D := F.toArithmeticData.familyDenominator coeff
  Polynomial.C n*(4*(Polynomial.X+Polynomial.C M.size+
    Polynomial.X*Polynomial.C (n*n*M*M).size+
    (2*Polynomial.X+1)*Polynomial.C D.size+3)+1)

@[simp] theorem width_eval (F : FixedField K n) (coeff : A→Fin n→ℚ) (b : ℕ) :
    (widthPolynomial F coeff).eval b=ArithmeticSize.bitBound F coeff b := by
  simp [widthPolynomial,ArithmeticSize.bitBound]

def runtimePolynomial (F : FixedField K n) (coeff : A→Fin n→ℚ)
    (labels : Encoding A Bool) : Polynomial ℕ :=
  let W := widthPolynomial F coeff
  let H := Polynomial.X
  let P := fieldProviders F
  let instruction := P.add.time.comp (3*W+1)+P.mul.time.comp (3*W+1)+
    14*W+18+(2*W+4)*Polynomial.C (2^18)+3+
    Polynomial.C (2*(labelBound labels+6))+4*((2*W+2)*H+1)+9
  H*instruction+6*W+16

def machine (F : FixedField K n) (coeff : A→Fin n→ℚ) (labels : Encoding A Bool) :=
  fieldInterpreter F labels (labelBound labels) (coefficients F coeff) (literals F coeff)

theorem formula_size_positive (p : RingFormula A) : 1≤p.size := by
  cases p <;> simp [RingFormula.size]

/-- The interpreter performs real parsing, rational arithmetic, stack copying
and output cleanup; its one fixed program is independent of formula size. -/
theorem evaluate_formula (F : FixedField K n) (coeff : A→Fin n→ℚ)
    (labels : Encoding A Bool) (aone : A) (hone : F.decode (coeff aone)=1)
    (p : RingFormula A) :
    ∃time,time≤(runtimePolynomial F coeff labels).eval p.size ∧
      Kernels.Executes (machine F coeff labels) ((codeEncoding labels).encode p.code)
        (F.encoding.encode (p.eval (coefficients F coeff))) time := by
  let W := ArithmeticSize.bitBound F coeff p.size
  have bound := p.structural_bound (coefficients F coeff) aone hone
  have hc : ∀a,(F.encoding.encode (coefficients F coeff a)).length≤W := by
    intro a
    exact ((ArithmeticSize.Bound.coefficient a).mono aone hone
      (formula_size_positive p)).encoded_length_le F coeff
  have hz : (F.encoding.encode 0).length≤W :=
    (ArithmeticSize.Bound.zero aone p.size).encoded_length_le F coeff
  have ho : (F.encoding.encode 1).length≤W :=
    (ArithmeticSize.Bound.one.mono aone hone (Nat.zero_le p.size)).encoded_length_le F coeff
  obtain ⟨time,ht,he⟩ := Interpreter.value_of_run labels (labelBound labels) F.encoding
    (coefficients F coeff) (literals F coeff) (fieldProviders F) (label_le labels)
    W hc hz ho p.code (p.eval (coefficients F coeff)) (p.trace (coefficients F coeff))
    (p.run_code _ []) (fun x hx => (bound.2 x hx).encoded_length_le F coeff)
  refine ⟨time,?_,he⟩
  simpa [runtimePolynomial,Interpreter.instructionBound,Kernels.timeBound,W] using ht

end
end Holant.Complexity.BinaryInterpolation.RingFormulaMachine
