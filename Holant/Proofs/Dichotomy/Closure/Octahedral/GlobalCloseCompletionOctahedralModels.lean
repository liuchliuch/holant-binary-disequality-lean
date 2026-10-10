import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicCards
import Holant.Projective.FiniteGroupFacts.Normalizers
import Holant.Certificates.OctahedralSeparator.GroupMarking
import Holant.Certificates.RainbowOrbit.GroupSources

/-! Coefficient extraction from the preserved marked-octahedral proof. The fixed source similarities are analytic group
coordinates only. Literal x/z images are certified by exact arithmetic;
neither these similarities nor a freely conjugated binary is a gadget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Coordinates.Models
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator

def basis (f : Form) : ComplexGL := Matrix.GeneralLinearGroup.mkOfDetNeZero
  (complexMatrix (conjugator f)) (complexMatrix_conjugator_det_ne_zero f)
def p (f : Form) : PGL2 ℂ := pglMk ℂ (basis f)
def group (f : Form) : Subgroup (PGL2 ℂ) :=
  (modelPGL .octahedral).map (MulAut.conj (p f)⁻¹).toMonoidHom
def xIndex : Form → Fin 24 := flipIndex
def zIndex : Form → Fin 24 := ![3,19,23,3]
def zScale : Form → Scalar := ![1,root/2,-(root/2),1]

theorem zero_group : group 0 = modelPGL .octahedral := by
  have hb : basis 0 = 1 := by
    apply Units.ext
    change complexMatrix (conjugator 0) = 1
    simpa only [conjugator,Matrix.cons_val_zero] using complexMatrix_q0
  have hi : (MulAut.conj (p 0)⁻¹).toMonoidHom=MonoidHom.id (PGL2 ℂ) := by
    ext z
    simp [p,hb]
  rw [group,hi,Subgroup.map_id]

theorem zScale_nonzero (f : Form) : zScale f ≠ 0 := by
  fin_cases f <;> decide +kernel

theorem x_raw (f : Form) : pull f flip = ms (flipScale f) (standard (xIndex f)) := by
  fin_cases f <;> decide +kernel
theorem z_raw (f : Form) : pull f (q 3) = ms (zScale f) (standard (zIndex f)) := by
  fin_cases f <;> decide +kernel

/-- The existing complete dictionary identifies each indexed GL value with
the SAME literal separator row; no new representative or scalar is chosen. -/
private theorem representativeGL_standard (i : Fin 24) :
    (representativeGL .octahedral i : ComplexMatrix)=complexMatrix (standard i) := by
  change goldenMatrix (octahedralRaw i)=complexMatrix (standard i)
  exact Holant.Certificates.RainbowOrbit.octahedralRaw_standard i

private theorem conjugate_class (f : Form) (U : ComplexGL) (i : Fin 24)
    (c : ℂ) (hc : c ≠ 0)
    (he : complexPull f (U : ComplexMatrix) = c • complexMatrix (standard i)) :
    p f * pglMk ℂ U * (p f)⁻¹ = (indexedPGL .octahedral i : PGL2 ℂ) := by
  change pglMk ℂ (basis f)*pglMk ℂ U*(pglMk ℂ (basis f))⁻¹ =
    pglMk ℂ (representativeGL .octahedral i)
  rw [←map_inv,←map_mul,←map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨c,hc,?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_mul,Matrix.GeneralLinearGroup.coe_inv]
  change (complexMatrix (conjugator f)*(U : ComplexMatrix))*
    (complexMatrix (conjugator f))⁻¹ = _
  rw [Matrix.mul_assoc,representativeGL_standard]
  exact he

theorem basis_x (f : Form) :
    p f*xClass*(p f)⁻¹ = (indexedPGL .octahedral (xIndex f) : PGL2 ℂ) := by
  apply conjugate_class f xGL (xIndex f) (embed (flipScale f))
    (embed_ne_zero (flipScale_nonzero f))
  have hx : (xGL : ComplexMatrix) = complexMatrix flip := by
    rw [complexMatrix_flip]
    ext a b
    cases a <;> cases b <;>
      simp [xGL,antidiagonalGL,antidiagonal,X,Signature.disequality]
  rw [hx,←complexMatrix_pull,x_raw,complexMatrix_ms]

theorem basis_z (f : Form) :
    p f*zClass*(p f)⁻¹ = (indexedPGL .octahedral (zIndex f) : PGL2 ℂ) := by
  have hz : (zGL : ComplexMatrix) = (-Complex.I) • complexMatrix (q 3) := by
    rw [complexMatrix_q]
    ext a b
    cases a <;> cases b <;>
      simp [zGL,diagonalGL,diagonal,quaternionBasis,Q3,Complex.I_sq]
  apply conjugate_class f zGL (zIndex f) ((-Complex.I)*embed (zScale f))
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (embed_ne_zero (zScale_nonzero f)))
  rw [hz,complexPull_smul,←complexMatrix_pull,z_raw,complexMatrix_ms,smul_smul]

theorem matrix_iff (f : Form) (U : ComplexGL) :
    pglMk ℂ U ∈ group f ↔ Direction f (U : ComplexMatrix) := by
  rw [group,Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply,inv_inv]
  change p f*pglMk ℂ U*(p f)⁻¹ ∈ modelPGL .octahedral ↔ _
  have he : p f*pglMk ℂ U*(p f)⁻¹ = pglMk ℂ (basis f*U*(basis f)⁻¹) := by
    simp only [p,map_mul,map_inv]
  rw [he,pglMk_mem_model_iff]
  simp only [Matrix.GeneralLinearGroup.coe_mul,Matrix.GeneralLinearGroup.coe_inv]
  change groupDirection .octahedral
    ((complexMatrix (conjugator f)*(U : ComplexMatrix))*(complexMatrix (conjugator f))⁻¹) ↔ _
  simpa only [complexPull,Matrix.mul_assoc] using (direction_iff_source_pull f (U : ComplexMatrix)).symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Coordinates.Models

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts Holant.Certificates.OctahedralSeparator
/-- Marked direction closure from the actual subgroup multiplication. -/
theorem direction_mul {f : Form} {U V : ComplexMatrix}
    (hU : Direction f U) (hV : Direction f V) : Direction f (U*V) := by
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero U hU.det_ne_zero
  let B := Matrix.GeneralLinearGroup.mkOfDetNeZero V hV.det_ne_zero
  have ha := (Coordinates.Models.matrix_iff f A).mpr hU
  have hb := (Coordinates.Models.matrix_iff f B).mpr hV
  have hab : pglMk ℂ (A*B)∈Coordinates.Models.group f := by
    rw [map_mul]
    exact (Coordinates.Models.group f).mul_mem ha hb
  exact (Coordinates.Models.matrix_iff f (A*B)).mp hab
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
