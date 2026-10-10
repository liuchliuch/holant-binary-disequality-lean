import Holant.Certificates.OctahedralSeparator.OutputData

namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem endpoint_coefficients : ∀ j : Fin 48, ¬outsideRow j →
    (∀ x : Word, (x 0 ^^ x 1 ^^ x 2 ^^ x 3)=true → endpointOutput j x=0) ∧
      endpointOutput j (fun _ => false) ≠ 0 ∧ endpointOutput j (fun _ => true) ≠ 0 := by
  intro j
  fin_cases j <;> decide +kernel

/-- Literal Eq4 in the unchanged computational basis. -/
def eq4 : Signature Scalar 4 := fun x => if x=(fun _ => false) ∨ x=(fun _ => true) then 1 else 0

theorem equality_exact : endpointOutput 34 = tensorScale (coeff (3/8) (1/4) 0 0) eq4 := by
  decide +kernel

theorem equality_scale_nonzero : (coeff (3/8) (1/4) 0 0 : Scalar) ≠ 0 := by decide +kernel

theorem endpoint_base_regular : ∀ j : Fin 48, ¬outsideRow j → (rowBase j).val<9 := by decide

theorem inverseConjugator_det_nonzero : ∀ f : Form, determinant (inverseConjugator f) ≠ 0 := by
  decide +kernel

theorem prepared_legs_nonsingular : ∀ f : Form, ∀ a : Fin 4,
    determinant (preparedLegs f a) ≠ 0 := by decide +kernel

end Holant.Certificates.OctahedralSeparator
