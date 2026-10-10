import Holant.Certificates.RainbowOrbit.MarkedGenerators
import Holant.Certificates.RainbowOrbit.NoRainbow

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem theta_mul (f : Form) (U V : BinaryMatrix) :
    complexTheta f (U*V)=complexTheta f U*complexTheta f V := by
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  change (markH f)⁻¹*((U*V)*markH f)=
    ((markH f)⁻¹*(U*markH f))*((markH f)⁻¹*(V*markH f))
  simp only [mul_assoc]
  rw [←mul_assoc (markH f),Matrix.mul_nonsing_inv _ hi,one_mul]

theorem theta_one (f : Form) : complexTheta f (1 : BinaryMatrix)=1 := by
  simp [complexTheta,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (complexMatrix_conjugator_det_ne_zero f))]

theorem marked_direction_inverse (f : Form) {U : BinaryMatrix} (hU : Direction f U) :
    Direction f (U⁻¹ : BinaryMatrix) := by
  obtain ⟨V,hV,rfl⟩ := (direction_iff_source_conjugate f U).mp hU
  have hv : (Matrix.of V).det≠0 := groupDirection_det_ne_zero .octahedral hV
  change Direction f ((complexTheta f (Matrix.of V))⁻¹ : BinaryMatrix)
  have he : (complexTheta f (Matrix.of V))⁻¹=complexTheta f (Matrix.of V)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [←theta_mul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hv),theta_one]
  rw [he]
  exact (direction_iff_source_conjugate f _).mpr ⟨_,direction_inverse .octahedral hV,rfl⟩

theorem marked_direction_transpose (f : Form) {U : BinaryMatrix} (hU : Direction f U) :
    Direction f U.transpose := by
  obtain ⟨V,hV,rfl⟩ := (direction_iff_source_conjugate f U).mp hU
  change Direction f (complexTheta f (Matrix.of V)).transpose
  have he : (complexTheta f (Matrix.of V)).transpose=
      complexTheta f (markS f*(Matrix.of V).transpose*markSinv f) := by
    rw [←conjugation_transposed_leg]
    simp [complexTheta,markH,Matrix.transpose_mul,Matrix.transpose_nonsing_inv,mul_assoc]
  rw [he]
  exact (direction_iff_source_conjugate f _).mpr ⟨_,RainbowOrbit.groupDirection_mul .octahedral
    (RainbowOrbit.groupDirection_mul .octahedral (markS_source f) (direction_transpose .octahedral hV))
    (markSinv_source f),rfl⟩

theorem standardMatrixFamily (g : PlatonicModel) : MatrixFamily (fun U => groupDirection g U) where
  one := direction_one g
  mul := RainbowOrbit.groupDirection_mul g
  inverse := direction_inverse g
  transpose := direction_transpose g
  smul := groupDirection_smul g
  nonsingular := groupDirection_det_ne_zero g

theorem markedMatrixFamily (f : Form) : MatrixFamily (Direction f) where
  one := (direction_iff_source_conjugate f _).mpr ⟨(1 : BinaryMatrix),direction_one .octahedral,(theta_one f).symm⟩
  mul := Direction.mul
  inverse := marked_direction_inverse f
  transpose := marked_direction_transpose f
  smul := Direction.smul
  nonsingular := Direction.det_ne_zero

end
end Holant.Certificates.RainbowOrbit
