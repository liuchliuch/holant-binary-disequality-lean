import Holant.Complexity.FixedFieldMachines.Semantics
import Holant.Algebraic.CoordinateSemiring

/-! Connect the actual machines to the executable coefficient semiring. The
runtime constructors use only rational table data; no semantic basis or law
proof is consulted by any transition. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose Holant.Algebraic
variable {n : ℕ}

noncomputable def coordinateAdditionComputes (R : RationalProvider) (D : ArithmeticData n) :
    Computes (pairEncoding (Coordinates.encoding D) (Coordinates.encoding D))
      (Coordinates.encoding D) (fun p => p.1 + p.2) :=
  recode (additionComputes R n) (fun p => (p.1.coeff, p.2.coeff))
    (fun _ => rfl) (fun _ => rfl)

noncomputable def coordinateMultiplicationComputes (R : RationalProvider) (D : ArithmeticData n) :
    Computes (pairEncoding (Coordinates.encoding D) (Coordinates.encoding D))
      (Coordinates.encoding D) (fun p => p.1 * p.2) :=
  recode (multiplicationComputes R D) (fun p => (p.1.coeff, p.2.coeff))
    (fun _ => rfl) (fun _ => rfl)

noncomputable def coordinateUnitComputes {α : Type} (ea : Encoding α Bool) (D : ArithmeticData n) :
    Computes ea (Coordinates.encoding D) (fun _ => 1) :=
  recode (unitComputes ea D) id (fun _ => rfl) (fun _ => rfl)

variable {K : Type} [Field K] [Algebra ℚ K]

/-- The semantic bridge uses the pre-existing field codec literally. -/
theorem fieldEncoding_eq_encoding (F : FixedField K n) : fieldEncoding F = F.encoding := rfl

noncomputable def existingFieldAdditionComputes (R : RationalProvider) (F : FixedField K n) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 + p.2) :=
  fieldAdditionComputes R F

noncomputable def existingFieldMultiplicationComputes (R : RationalProvider) (F : FixedField K n) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 * p.2) :=
  fieldMultiplicationComputes R F

end Holant.Complexity.FixedFieldMachines
