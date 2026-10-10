import Holant.Certificates.OctahedralSeparator.GroupRepresentatives

/-! Actual marked-group closure and availability of physical native-X binary
vertices.  All membership certificates retain their exact nonzero scale. -/
namespace Holant.Certificates.OctahedralSeparator
noncomputable section
open Holant
open Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Direction

theorem standard (f : Form) (k : Fin 24) :
    Direction f (complexMatrix (theta f (OctahedralSeparator.standard k))) :=
  ⟨1,one_ne_zero,k,by simp⟩

theorem smul {f : Form} {U : Matrix Bool Bool ℂ} (hU : Direction f U)
    {c : ℂ} (hc : c ≠ 0) : Direction f (c • U) := by
  obtain ⟨d,hd,k,rfl⟩ := hU
  exact ⟨c*d,mul_ne_zero hc hd,k,by rw [smul_smul]⟩

theorem det_ne_zero {f : Form} {U : Matrix Bool Bool ℂ} (hU : Direction f U) :
    Matrix.det U ≠ 0 := by
  obtain ⟨V,hV,rfl⟩ := (direction_iff_source_conjugate f U).mp hU
  have hH := complexMatrix_conjugator_det_ne_zero f
  have hV' : Matrix.det (Matrix.of V) ≠ 0 := groupDirection_det_ne_zero .octahedral hV
  simp only [complexTheta,Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
  exact mul_ne_zero (inv_ne_zero hH) (mul_ne_zero hV' hH)

end Direction

def flipIndex : Form → Fin 24 := ![1,18,1,19]
def flipScale : Form → Scalar := ![-imag,coeff 0 0 0 (-1/2),-imag,coeff 0 0 0 (-1/2)]

theorem flipScale_nonzero : ∀ f : Form, flipScale f ≠ 0 := by decide +kernel

theorem flip_marked_certificate : ∀ f : Form,
    flip = ms (flipScale f) (theta f (standard (flipIndex f))) := by
  intro f
  fin_cases f <;> decide +kernel

def correctionIndex : Form → Fin 24 := ![0,1,12,17]
def correctionScale : Form → Scalar :=
  ![1,coeff 0 (1/8) 0 (-1/8),coeff (1/4) (1/4) 0 0,coeff (1/4) (1/4) 0 0]

theorem correctionScale_nonzero : ∀ f : Form, correctionScale f ≠ 0 := by decide +kernel

theorem sInverse_standard_certificate : ∀ f : Form,
    sInverse f = ms (correctionScale f) (standard (correctionIndex f)) := by decide +kernel

theorem direction_flip (f : Form) : Direction f (complexMatrix flip) := by
  refine ⟨embed (flipScale f),embed_ne_zero (flipScale_nonzero f),flipIndex f,?_⟩
  rw [flip_marked_certificate f,complexMatrix_ms]

theorem direction_X (f : Form) : Direction f (Matrix.of X) := by
  simpa only [complexMatrix_flip] using direction_flip f

theorem direction_correction (f : Form) : Direction f (complexMatrix (correction f)) := by
  refine ⟨embed (correctionScale f),embed_ne_zero (correctionScale_nonzero f),correctionIndex f,?_⟩
  rw [correction,sInverse_standard_certificate f,theta_ms,complexMatrix_ms]

end
end Holant.Certificates.OctahedralSeparator
