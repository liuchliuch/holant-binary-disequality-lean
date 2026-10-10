import Holant.Certificates.RainbowOrbit.PointAction
import Holant.Certificates.OctahedralSeparator.GroupMembership
import Holant.Certificates.OctahedralSeparator.GroupMatrixInverses

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
open OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def markLegs (f : Form) : Legs := fun j => complexMatrix (coefficientLegs f j)

def markH (f : Form) : BinaryMatrix := complexMatrix (conjugator f)
def markS (f : Form) : BinaryMatrix := markH f*(markH f).transpose
def markSinv (f : Form) : BinaryMatrix := (markH f)⁻¹.transpose*(markH f)⁻¹

theorem markH_det (f : Form) : (markH f).det≠0 := complexMatrix_conjugator_det_ne_zero f

theorem markLegs_eq (f : Form) : markLegs f=![ (markH f)⁻¹,(markH f).transpose,
    (markH f)⁻¹,(markH f).transpose] := by
  funext j
  fin_cases j <;> simp [markLegs,coefficientLegs,markH,complexMatrix_inverseConjugator]

theorem markLegs_det (f : Form) : ∀j,(markLegs f j).det≠0 := by
  intro j
  rw [markLegs_eq]
  fin_cases j <;> simp [Matrix.det_nonsing_inv,markH_det]

theorem markSinv_source (f : Form) : groupDirection .octahedral (markSinv f) := by
  have he : markSinv f=complexMatrix (sInverse f) := by
    simp [markSinv,markH,sInverse,complexMatrix_inverseConjugator]
  rw [he,sInverse_standard_certificate f,complexMatrix_ms]
  exact groupDirection_smul .octahedral
    ((source_group_iff_standard _).mpr ⟨1,one_ne_zero,correctionIndex f,by simp⟩)
    (embed_ne_zero (correctionScale_nonzero f))

theorem markS_mul_markSinv (f : Form) : markS f*markSinv f=1 := by
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  have ht : (markH f).transpose*(markH f)⁻¹.transpose=(1 : BinaryMatrix) := by
    rw [←Matrix.transpose_mul,Matrix.nonsing_inv_mul _ hi,Matrix.transpose_one]
  simp only [markS,markSinv,mul_assoc]
  rw [←mul_assoc (markH f).transpose,ht,one_mul,Matrix.mul_nonsing_inv _ hi]

theorem markSinv_mul_markS (f : Form) : markSinv f*markS f=1 := by
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  have ht : (markH f)⁻¹.transpose*(markH f).transpose=(1 : BinaryMatrix) := by
    rw [←Matrix.transpose_mul,Matrix.mul_nonsing_inv _ hi,Matrix.transpose_one]
  simp only [markS,markSinv,mul_assoc]
  rw [←mul_assoc (markH f)⁻¹,Matrix.nonsing_inv_mul _ hi,one_mul,ht]

theorem markS_source (f : Form) : groupDirection .octahedral (markS f) := by
  have he : markS f=(markSinv f)⁻¹ := Matrix.inv_eq_left_inv (markS_mul_markSinv f) |>.symm
  rw [he]
  exact direction_inverse .octahedral (markSinv_source f)

/-- Exact ordered matching transport, including the source's orientation factors. -/
theorem mark_P0 (f : Form) (U V : BinaryMatrix) :
    act (markLegs f) (P0 U V)=P0 (complexTheta f U) (complexTheta f V) := by
  rw [markLegs_eq,act_P0]
  simp [complexTheta,markH,mul_assoc]

theorem mark_P1 (f : Form) (U V : BinaryMatrix) :
    act (markLegs f) (P1 U V)=
      P1 (complexTheta f (U*markSinv f)) (complexTheta f (markS f*V)) := by
  rw [markLegs_eq,act_P1]
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  have h1 : complexTheta f (U*markSinv f)=(markH f)⁻¹*U*(markH f)⁻¹.transpose := by
    change (markH f)⁻¹*((U*((markH f)⁻¹.transpose*(markH f)⁻¹))*markH f)=_
    simp only [mul_assoc]
    simp only [Matrix.nonsing_inv_mul _ hi,mul_one]
  have h2 : complexTheta f (markS f*V)=(markH f).transpose*V*markH f := by
    change (markH f)⁻¹*(((markH f*(markH f).transpose)*V)*markH f)=_
    simp only [←mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hi,one_mul]
  rw [h1,h2]
  simp

theorem mark_P2 (f : Form) (U V : BinaryMatrix) :
    act (markLegs f) (P2 U V)=
      P2 (complexTheta f U) (complexTheta f (markS f*V*markSinv f)) := by
  rw [markLegs_eq,act_P2]
  have hi := isUnit_iff_ne_zero.mpr (markH_det f)
  have h2 : complexTheta f (markS f*V*markSinv f)=
      (markH f).transpose*V*(markH f)⁻¹.transpose := by
    change (markH f)⁻¹*((((markH f*(markH f).transpose)*V)*
      ((markH f)⁻¹.transpose*(markH f)⁻¹))*markH f)=_
    simp only [mul_assoc]
    simp only [Matrix.nonsing_inv_mul _ hi,mul_one]
    simp only [←mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hi,one_mul]
  rw [h2]
  simp [complexTheta,markH,mul_assoc]

end
end Holant.Certificates.RainbowOrbit
