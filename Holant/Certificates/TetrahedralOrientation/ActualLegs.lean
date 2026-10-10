import Holant.Certificates.TetrahedralOrientation.PhysicalShape

/-! Every dressing is an actual invertible tetrahedral resource, with the
source's internal-first B_L = X Lᵀ and our equivalent boundary-first LX order. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem Gplus_direction : groupDirection .tetrahedral Gplus := by
  refine ⟨1,one_ne_zero,Gplus,Or.inr ⟨fun _ => false,?_⟩,by simp⟩
  funext a b
  simp [Gplus,quaternion,signBit]

theorem Gminus_direction : groupDirection .tetrahedral Gminus := by
  refine ⟨1,one_ne_zero,Gminus,Or.inr ⟨![false,false,true],?_⟩,by simp⟩
  funext a b
  simp [Gminus,quaternion,signBit,sub_eq_add_neg]

theorem legs_direction (s : Orientation) (j : Fin 4) :
    groupDirection .tetrahedral (legs s j) := by
  have h0 : groupDirection .tetrahedral Q0 := quaternion_axis_direction _ 0
  have h1 : groupDirection .tetrahedral Q1 := quaternion_axis_direction _ 1
  fin_cases s <;> fin_cases j <;> first | exact h0 | exact h1 | exact Gplus_direction | exact Gminus_direction

theorem legs_nonsingular (s : Orientation) (j : Fin 4) :
    Matrix.det (Matrix.of (legs s j)) ≠ 0 :=
  groupDirection_det_ne_zero _ (legs_direction s j)

/-- Exact source/internal-first port convention. -/
def sourceDressing (L : Binary) : Binary := Kernel.mul Signature.disequality (Kernel.transpose L)

theorem nativeLeg_transpose_source (L : Binary) : nativeLeg L = Kernel.transpose (sourceDressing L) := by
  funext a b
  simp [nativeLeg,sourceDressing,Kernel.transpose,Kernel.mul_disequality,Kernel.disequality_mul]

theorem nativeLeg_transfer (L : Binary) : multiply (nativeLeg L) X = L := by
  funext a b
  simp [multiply,nativeLeg,Kernel.mul_disequality,X,Signature.disequality]
  cases b <;> simp

theorem nativeLeg_actual (s : Orientation) (j : Fin 4) :
    groupDirection .tetrahedral (multiply (nativeLeg (legs s j)) X) := by
  rw [nativeLeg_transfer]
  exact legs_direction s j

theorem sourceDressing_actual (s : Orientation) (j : Fin 4) :
    groupDirection .tetrahedral (multiply (sourceDressing (legs s j)) X) := by
  apply (groupDirection_right_X_iff _ _).mpr
  have ht := groupDirection_transpose .tetrahedral
    ((groupDirection_right_X_iff _ _).mp (nativeLeg_actual s j))
  have he : transpose (nativeLeg (legs s j)) = sourceDressing (legs s j) := by
    rw [nativeLeg_transpose_source]
    rfl
  rwa [he] at ht

/-- The separate I vertex is also an available tetrahedral binary. -/
theorem equality_actual : groupDirection .tetrahedral (multiply Q0 X) := Q0_X_direction _

end
end Holant.Certificates.TetrahedralOrientation
