import Holant.Complexity.FixedFieldMachines.RationalCircuit
import Holant.Algebraic.FixedFieldInverse

/-! Actual polynomial Boolean-stack inversion in a fixed number field.
The input is the original rational coordinate vector. All determinant and
reciprocal operations compile to ordinary rational machines; no semantic
basis evaluation or field-inverse primitive occurs during execution. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose Holant.Algebraic
open scoped BigOperators
noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

def multiplicationMatrixEntryComputes (D : ArithmeticData n) (k j : Fin n) :
    Computes (vectorEncoding n) rationalEncoding (fun v => D.multiplicationMatrix v k j) := by
  change Computes (vectorEncoding n) rationalEncoding (fun v : Fin n→ℚ => ∑i,v i*D.mulTable i j k)
  exact RationalCircuit.sum Finset.univ (fun (v : Fin n→ℚ) i => v i*D.mulTable i j k)
    (fun i => RationalCircuit.mul (coordinateComputes n i)
      (constantComputes (vectorEncoding n) rationalEncoding (D.mulTable i j k)))

def multiplicationDeterminantComputes (D : ArithmeticData n) :
    Computes (vectorEncoding n) rationalEncoding (fun v => (D.multiplicationMatrix v).det) :=
  RationalCircuit.determinant D.multiplicationMatrix (multiplicationMatrixEntryComputes D)

def cramerDeterminantComputes (D : ArithmeticData n) (k : Fin n) :
    Computes (vectorEncoding n) rationalEncoding
      (fun v => ((D.multiplicationMatrix v).updateCol k D.unitCode).det) := by
  apply RationalCircuit.determinant
  intro i j
  by_cases h : j=k
  · subst j
    exact congrComputes (constantComputes (vectorEncoding n) rationalEncoding (D.unitCode i))
      (fun _ => by simp)
  · exact congrComputes (multiplicationMatrixEntryComputes D i j)
      (fun _ => by simp [Matrix.updateCol,h])

/-- A real canonical-coordinate inversion program, total also at zero. -/
def inverseCoordinatesComputes (D : ArithmeticData n) :
    Computes (vectorEncoding n) (vectorEncoding n) D.inverseCode := by
  apply assembleComputes
  intro k
  exact congrComputes (RationalCircuit.mul
    (RationalCircuit.inv (multiplicationDeterminantComputes D))
    (cramerDeterminantComputes D k))
    (fun v => (D.inverseCode_apply v k).symm)

variable {K : Type} [Field K] [Algebra ℚ K]

/-- The original field encoding is unchanged; inverse correctness is derived
from multiplication-table semantics and the faithful basis map. -/
def fieldInverseComputes (F : FixedField K n) :
    Computes F.encoding F.encoding (fun x : K => x⁻¹) := by
  apply recode (inverseCoordinatesComputes F.toArithmeticData) F.decode.symm (fun _ => rfl)
  intro x
  change (vectorEncoding n).encode (F.toArithmeticData.inverseCode (F.decode.symm x))=
    (vectorEncoding n).encode (F.decode.symm x⁻¹)
  congr 1
  apply F.decode_injective
  simp [F.decode_inverseCode]

theorem fieldInverse_inFP (F : FixedField K n) :
    InFP F.encoding F.encoding (fun x : K => x⁻¹) := (fieldInverseComputes F).inFP

def fieldDivisionComputes (F : FixedField K n) :
    Computes (pairEncoding F.encoding F.encoding) F.encoding (fun p : K×K => p.1/p.2) :=
  congrComputes ((pairComputes (Wiring.firstComputes F.encoding F.encoding)
    ((Wiring.secondComputes F.encoding F.encoding).andThen (fieldInverseComputes F))).andThen
      (Concrete.fieldMultiplication F)) (fun _ => (div_eq_mul_inv _ _).symm)

end
end Holant.Complexity.FixedFieldMachines
