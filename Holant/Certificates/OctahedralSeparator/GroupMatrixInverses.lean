import Holant.Certificates.OctahedralSeparator.MatrixSemantics

/-! Exact adjugate inverses agree with the genuine complex matrix inverse. -/
namespace Holant.Certificates.OctahedralSeparator
noncomputable section
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false

/-- Adjugate divided by the determinant in Q(sqrt2,i). -/
def scalarInverse (U : Mat) : Mat := ms (determinant U)⁻¹
  (mat (U true true) (-U false true) (-U true false) (U false false))

theorem complexMatrix_scalarInverse (U : Mat) (hU : determinant U ≠ 0) :
    complexMatrix (scalarInverse U) = (complexMatrix U)⁻¹ := by
  have hd : Matrix.det (Matrix.of (complexMatrix U)) ≠ 0 := by
    change Matrix.det (complexMatrix U) ≠ 0
    rw [← embed_determinant]
    exact embed_ne_zero hU
  change complexMatrix (scalarInverse U) = (Matrix.of (complexMatrix U))⁻¹
  rw [binary_matrix_inverse _ hd]
  ext a b
  cases a <;> cases b <;>
    simp [scalarInverse,ms,mat,complexMatrix,embed_mul,embed_inv,
      adjugateBinary,binaryDeterminant,determinant]

theorem scalarInverse_right (U : Mat) (hU : determinant U ≠ 0) :
    mm U (scalarInverse U) = q 0 := by
  apply complexMatrix_injective
  rw [complexMatrix_mm,complexMatrix_scalarInverse U hU,complexMatrix_q0]
  apply Matrix.mul_nonsing_inv
  exact isUnit_iff_ne_zero.mpr (by rw [← embed_determinant]; exact embed_ne_zero hU)

theorem scalarInverse_left (U : Mat) (hU : determinant U ≠ 0) :
    mm (scalarInverse U) U = q 0 := by
  apply complexMatrix_injective
  rw [complexMatrix_mm,complexMatrix_scalarInverse U hU,complexMatrix_q0]
  apply Matrix.nonsing_inv_mul
  exact isUnit_iff_ne_zero.mpr (by rw [← embed_determinant]; exact embed_ne_zero hU)

theorem sMatrix_sInverse : ∀ f : Form, mm (sMatrix f) (sInverse f) = q 0 := by
  decide +kernel

theorem complexMatrix_sInverse (f : Form) :
    complexMatrix (sInverse f) = (complexMatrix (sMatrix f))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← complexMatrix_mm,sMatrix_sInverse f,complexMatrix_q0]

end
end Holant.Certificates.OctahedralSeparator
