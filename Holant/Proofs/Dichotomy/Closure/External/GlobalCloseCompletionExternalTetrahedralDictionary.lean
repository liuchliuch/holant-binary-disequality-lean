import Holant.Proofs.Dichotomy.Closure.External.GlobalCloseCompletionExternalTetrahedralFrame
import Holant.Certificates.TetrahedralPreservers.ExternalCoordinates

/-! Literal external tetrahedral dictionary in the original current basis.
Both physical marks fix the analytic group coordinate, and actual reversal
removes its remaining centralizer ambiguity. No conjugator is a gate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionExternalTetrahedralDictionary
open Holant.Certificates
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedReversalOvergroup.Ambient
namespace Frame
export GlobalCloseCompletionExternalTetrahedralFrame (aligned map_conj_mul)
end Frame

def basis : ComplexGL := Matrix.GeneralLinearGroup.mkOfDetNeZero
  (complexMatrix (conjugator 2)) (complexMatrix_conjugator_det_ne_zero 2)
def p : PGL2 ℂ := pglMk ℂ basis
def group : Subgroup (PGL2 ℂ) := (modelPGL .tetrahedral).map (MulAut.conj p⁻¹).toMonoidHom

theorem direction_iff_pull (U : ComplexMatrix) :
    RainbowOrbit.External.Direction U ↔ groupDirection .tetrahedral (complexPull 2 U) := by
  constructor
  · rintro ⟨k,c,hc,rfl⟩
    rw [RainbowOrbit.External.representative_eq_theta,complexPull_smul,complexPull_complexTheta]
    exact groupDirection_smul .tetrahedral (RainbowOrbit.representative_mem _ _) hc
  · intro h
    obtain ⟨k,c,hc,hk⟩ := (RainbowOrbit.complete .tetrahedral _).mp h
    refine ⟨k,c,hc,?_⟩
    have hh := congrArg (complexTheta 2) hk
    simpa only [complexTheta_complexPull,complexTheta_smul,
      RainbowOrbit.External.representative_eq_theta] using hh

/-- Complete scalar-closed dictionary, for every invertible matrix. -/
theorem matrix_iff (U : ComplexGL) :
    pglMk ℂ U ∈ group ↔ RainbowOrbit.External.Direction (U : ComplexMatrix) := by
  rw [group,Subgroup.map_equiv_eq_comap_symm']
  change (MulAut.conj p⁻¹).symm (pglMk ℂ U) ∈ modelPGL .tetrahedral ↔ _
  simp only [MulAut.conj_symm_apply,inv_inv]
  have he : p*pglMk ℂ U*p⁻¹=pglMk ℂ (basis*U*basis⁻¹) := by
    simp only [p,map_mul,map_inv]
  rw [he,pglMk_mem_model_iff]
  simp only [Matrix.GeneralLinearGroup.coe_mul,Matrix.GeneralLinearGroup.coe_inv]
  change groupDirection .tetrahedral
    ((complexMatrix (conjugator 2) * (U : ComplexMatrix)) *
      (complexMatrix (conjugator 2))⁻¹) ↔ _
  simpa only [complexPull,Matrix.mul_assoc] using (direction_iff_pull (U : ComplexMatrix)).symm

theorem basis_x : p*xClass*p⁻¹=xClass := by
  have raw : mm (conjugator 2) flip=mm flip (conjugator 2) := by decide +kernel
  have hx : (xGL : ComplexMatrix)=complexMatrix flip := by
    rw [complexMatrix_flip]
    ext i j
    cases i <;> cases j <;>
      simp [xGL,antidiagonalGL,antidiagonal,Holant.Certificates.MatchingProductBridge.X,
        Signature.disequality]
  have hm : (basis : ComplexMatrix)*(xGL : ComplexMatrix)=
      (xGL : ComplexMatrix)*(basis : ComplexMatrix) := by
    change complexMatrix (conjugator 2)*(xGL : ComplexMatrix)=
      (xGL : ComplexMatrix)*complexMatrix (conjugator 2)
    rw [hx]
    have h := congrArg complexMatrix raw
    simpa only [complexMatrix_mm] using h
  have hc : Commute p xClass := (commute_mk_iff_scalar basis xGL).mpr
    ⟨1,one_ne_zero,by simpa only [one_smul] using hm⟩
  rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]

/-- The actual reference j is the odd involution at index 23, with its
nonzero sqrt(2)/2 and Pauli phase both retained. -/
theorem basis_z : p*zClass*p⁻¹=(indexedPGL .octahedral (23 : Fin 24) : PGL2 ℂ) := by
  have raw : pull 2 (q 3)=ms (-(root/2)) (standard 23) := by decide +kernel
  have hr : (-(root/2) : Scalar)≠0 := by decide +kernel
  have hz : (zGL : ComplexMatrix)=(-Complex.I) • complexMatrix (q 3) := by
    rw [complexMatrix_q]
    ext i j
    cases i <;> cases j <;>
      simp [zGL,diagonalGL,diagonal,quaternionBasis,Q3,Complex.I_sq]
  change pglMk ℂ basis*pglMk ℂ zGL*(pglMk ℂ basis)⁻¹=
    pglMk ℂ (representativeGL .octahedral (23 : Fin 24))
  rw [←map_inv,←map_mul,←map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨(-Complex.I)*embed (-(root/2)),
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (embed_ne_zero hr),?_⟩
  simp only [Matrix.GeneralLinearGroup.coe_mul,Matrix.GeneralLinearGroup.coe_inv]
  change (complexMatrix (conjugator 2)*(zGL : ComplexMatrix))*
    (complexMatrix (conjugator 2))⁻¹ = _
  rw [hz,Matrix.mul_smul,Matrix.smul_mul]
  rw [Matrix.mul_assoc,←complexPull,←complexMatrix_pull,raw,complexMatrix_ms]
  rw [←RainbowOrbit.octahedralRaw_standard]
  change (-Complex.I) • (embed (-(root/2)) • RainbowOrbit.representative .octahedral (23 : Fin 24))=_
  rw [smul_smul]
  rfl

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (identity : (⟨2,binarySignature (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
local notation "current" => ClosureMarkedDihedral.Source.group phi F torsion

include identity in
theorem pauli_normalizes : pauliSubgroup ≤ Subgroup.normalizer (current : Set (PGL2 ℂ)) := by
  change Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  intro q hq
  rcases Set.mem_insert_iff.mp hq with rfl | hq
  · exact (current).le_normalizer (ClosureMarkedDihedral.Source.nativeX_mem phi F torsion identity)
  · have hz : q=zClass := Set.mem_singleton_iff.mp hq
    subst q
    exact actual_normalizedZ phi F torsion

include identity in
theorem current_group
    (semantic : HasModel (overgroup phi F torsion) (.platonic .octahedral))
    (actual : HasModel current (.platonic .tetrahedral))
    (outside : zClass∉current) : current=group := by
  obtain ⟨g,hG,hx,hz⟩ := Frame.aligned phi F torsion identity semantic actual outside
  let n : PGL2 ℂ := p⁻¹*g
  have hnx : n*xClass*n⁻¹=xClass := by
    calc
      _ = p⁻¹*(g*xClass*g⁻¹)*p := by dsimp [n]; group
      _ = p⁻¹*xClass*p := by rw [hx]
      _ = xClass := by
        calc
          p⁻¹*xClass*p = p⁻¹*(p*xClass*p⁻¹)*p := by rw [basis_x]
          _ = xClass := by group
  have hnz : n*zClass*n⁻¹=zClass := by
    calc
      _ = p⁻¹*(g*zClass*g⁻¹)*p := by dsimp [n]; group
      _ = p⁻¹*(p*zClass*p⁻¹)*p := by rw [hz,basis_z]
      _ = zClass := by group
  have commute_of_fixed {q : PGL2 ℂ} (hq : n*q*n⁻¹=q) : Commute n q := by
    have h := congrArg (fun r : PGL2 ℂ => r*n) hq
    change n*q=q*n
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  have hp : n ∈ pauliSubgroup := (pauli_membership n).mpr
    ((commute_x_z_iff n).mp ⟨commute_of_fixed hnx,commute_of_fixed hnz⟩)
  have hn := Subgroup.mem_normalizer_iff_map_conj_eq.mp (pauli_normalizes phi F torsion identity hp)
  calc
    current = (current).map (MulAut.conj n).toMonoidHom := hn.symm
    _ = (modelPGL .tetrahedral).map (MulAut.conj p⁻¹).toMonoidHom := by
      rw [show n=p⁻¹*g from rfl,Frame.map_conj_mul,hG]
    _ = group := rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionExternalTetrahedralDictionary
end
