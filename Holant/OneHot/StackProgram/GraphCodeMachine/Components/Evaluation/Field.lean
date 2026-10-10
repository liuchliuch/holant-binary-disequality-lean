import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation.GrammarBound
import Holant.Complexity.FixedFieldMachines.StackEvaluatorBridge

/-! A fixed algebraic family supplies canonical rational-vector literals and real
field operators. Bounds cover the grammar's actual result and complete trace. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation
open Turing Computability Holant.Algebraic Holant.Complexity
open Holant.OneHot.StackProgram.Machine
open FixedFieldMachines.StackEvaluatorBridge
variable {A K : Type} [Fintype A] [Field K] [Algebra ℚ K] {n : ℕ}
variable (F : FixedField K n) (table : A → Fin n → ℚ)

noncomputable def coefficients : A → K := fun a => F.decode (table a)

/-- Runtime constants consist solely of the fixed rational table and unit coordinates. -/
def literals : Kernels.Literals F.encoding (coefficients F table) where
  table.words a := (vectorEncoding n).encode (table a)
  table.correct a := (F.encoding_decode (table a)).symm
  zeroWord := (vectorEncoding n).encode 0
  oneWord := (vectorEncoding n).encode F.unitCode
  zero_correct := by simpa using (F.encoding_decode (0 : Fin n → ℚ)).symm
  one_correct := by simpa using (F.encoding_decode F.unitCode).symm

noncomputable def width (L : ℕ) : ℕ :=
  ArithmeticSize.bitBound F (ArithmeticSize.withUnit F table) L + literalWidth (literals F table)

noncomputable def widthPolynomial : Polynomial ℕ :=
  let family := ArithmeticSize.withUnit F table
  let M := F.toArithmeticData.familyBound family
  let D := F.toArithmeticData.familyDenominator family
  Polynomial.C n * (4 * (Polynomial.X + Polynomial.C M.size +
    Polynomial.X * Polynomial.C (n * n * M * M).size +
    (2 * Polynomial.X + 1) * Polynomial.C D.size + 3) + 1) +
    Polynomial.C (literalWidth (literals F table))

@[simp] theorem widthPolynomial_eval (L : ℕ) :
    (widthPolynomial F table).eval L = width F table L := by
  simp [widthPolynomial, width, ArithmeticSize.bitBound]

/-- No certificate is assumed: the actual encoded descriptor grammar proves it. -/
theorem encoded_trace_bound (labels : Encoding A Bool) (ds : List (Descriptor A)) :
    (F.encoding.encode (value (coefficients F table) ds)).length ≤
      width F table ((listEncoding labels).encode ds).length ∧
    ∀ x ∈ (productProgram (coefficients F table) ds).values,
      (F.encoding.encode x).length ≤ width F table ((listEncoding labels).encode ds).length := by
  let family := fun a => F.decode (ArithmeticSize.withUnit F table a)
  have hunit : family none = 1 := ArithmeticSize.decode_withUnit_none F table
  have hc : ∀ a, ArithmeticSize.Bound family 1 (coefficients F table a) := by
    intro a
    exact ArithmeticSize.family_bound F table ⟨a, rfl⟩
  have h := product_bound (coefficients F table) family none hunit hc ds
  have hs := productBudget_le labels ds
  have hb := ArithmeticSize.bitBound_mono F (ArithmeticSize.withUnit F table) hs
  constructor
  · exact ((h.1.encoded_length_le F (ArithmeticSize.withUnit F table)).trans hb).trans (Nat.le_add_right _ _)
  · intro x hx
    exact (((h.2 x hx).encoded_length_le F (ArithmeticSize.withUnit F table)).trans hb).trans (Nat.le_add_right _ _)

end Holant.OneHot.StackProgram.GraphCodeMachine.Components.Evaluation
