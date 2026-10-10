import Holant.Complexity.FixedFieldMachines.ScalarPower.Compile
import Holant.Complexity.FixedFieldMachines.Concrete

/-! Exact input-dependent correction by a power of a fixed nonzero scalar.
Only the fixed inverse's rational coordinates are compiled into the program;
there is no runtime field-inversion oracle or free scalar gadget. -/
namespace Holant.Complexity.FixedFieldMachines.ScalarPower
open Computability BinaryCompose Holant.Algebraic
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

noncomputable def multiplyPower (F : FixedField K n) (c : Fin n → ℚ) :
    Computes (pairEncoding F.encoding GraphPreprocessing.UnaryBinary.unaryEncoding)
      F.encoding (fun p : K × ℕ => p.1 * (F.decode c)^p.2) :=
  congrComputes ((rightMapComputes F.encoding (computes F c)).andThen
    (Concrete.fieldMultiplication F)) (fun _ => rfl)

/-- The normalization is fixed before any input or oracle answer is supplied. -/
noncomputable def correction (F : FixedField K n) (scale : K) :
    Computes (pairEncoding F.encoding GraphPreprocessing.UnaryBinary.unaryEncoding)
      F.encoding (fun p : K × ℕ => p.1 * (scale⁻¹)^p.2) :=
  congrComputes (multiplyPower F (F.decode.symm scale⁻¹)) (fun p => by simp)

theorem cancel_scale_power (scale y : K) (hscale : scale ≠ 0) (k : ℕ) :
    (scale^k*y) * (scale⁻¹)^k = y := by
  rw [mul_right_comm, ← mul_pow, mul_inv_cancel₀ hscale, one_pow, one_mul]

/-- A proved exact query-value relation turns the actual answer correction into
its original answer, with no operation on semantic values added to the machine. -/
noncomputable def correct_answer (F : FixedField K n) (scale y : K) (hscale : scale ≠ 0) (k : ℕ) :
    Turing.TM2OutputsInTime (correction F scale).machine.computer
      ((pairEncoding F.encoding GraphPreprocessing.UnaryBinary.unaryEncoding).encode (scale^k*y,k))
      (some (F.encoding.encode y))
      ((correction F scale).time.eval
        ((pairEncoding F.encoding GraphPreprocessing.UnaryBinary.unaryEncoding).encode (scale^k*y,k)).length) := by
  simpa only [cancel_scale_power scale y hscale k] using (correction F scale).outputs (scale^k*y,k)

end Holant.Complexity.FixedFieldMachines.ScalarPower
