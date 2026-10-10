import Holant.Certificates.MatchingProductBridge.GroupOperations

namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binaryFinEquiv : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := if i = 0 then false else true
  left_inv := by decide
  right_inv := by decide

def binaryDeterminant (U : Binary) : ℂ := U false false * U true true-U false true * U true false

theorem binaryDeterminant_eq_det (U : Binary) : binaryDeterminant U = Matrix.det (Matrix.of U) := by
  have h := Matrix.det_reindex_self binaryFinEquiv (Matrix.of U)
  rw [Matrix.det_fin_two] at h
  simpa [binaryDeterminant,Matrix.reindex_apply,binaryFinEquiv] using h

theorem adjugate_product (U : Binary) :
    Matrix.of U * Matrix.of (adjugateBinary U) = binaryDeterminant U • (1 : Matrix Bool Bool ℂ) := by
  ext a b
  cases a <;> cases b <;>
    simp [Matrix.mul_apply,Matrix.one_apply,adjugateBinary,binaryDeterminant] <;> ring

/-- The inverse in the actual matrix API agrees with the explicit binary adjugate formula. -/
theorem binary_matrix_inverse (U : Binary) (hU : Matrix.det (Matrix.of U) ≠ 0) :
    (Matrix.of U)⁻¹ = (binaryDeterminant U)⁻¹ • Matrix.of (adjugateBinary U) := by
  have hd : binaryDeterminant U ≠ 0 := by rwa [binaryDeterminant_eq_det]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul,adjugate_product,smul_smul]
  simp [hd]

/-- The explicit matrix-inverse instance, never pointwise inversion of entries. -/
def binaryInverse (U : Binary) : Binary := fun a b =>
  (@Inv.inv (Matrix Bool Bool ℂ) Matrix.inv (Matrix.of U)) a b

def binaryInverseTranspose (U : Binary) : Binary := transpose (binaryInverse U)

theorem groupDirection_inverse (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (binaryInverse U) := by
  have hd := groupDirection_det_ne_zero g hU
  have he : binaryInverse U = (binaryDeterminant U)⁻¹ • adjugateBinary U := by
    have hh := binary_matrix_inverse U hd
    exact congrArg (fun M : Matrix Bool Bool ℂ => fun a b => M a b) hh
  rw [he]
  exact groupDirection_smul g (groupDirection_adjugate g hU)
    (inv_ne_zero (by rwa [binaryDeterminant_eq_det]))

theorem groupDirection_inverseTranspose (g : PlatonicModel) {U : Binary} (hU : groupDirection g U) :
    groupDirection g (binaryInverseTranspose U) :=
  groupDirection_transpose g (groupDirection_inverse g hU)

end
end Holant.Certificates.MatchingProductBridge
