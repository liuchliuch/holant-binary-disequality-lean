import Holant.Proofs.Closure.ClosureMarkedReversalRouting
import Holant.Proofs.Closure.ClosureMarkedDihedralCoordinates

/-! Constructed native-Y/B marked branch. The algebraic basis I-iX is fixed,
not selected by an arbitrary complex conjugacy. It normalizes the real actual
native-Y centralizer branch to the already proved reflected-torus construction,
keeps the same physical edge exactly (-2i) I, and keeps ordered reversal.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralB
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedCyclic (coordinateGL)
open ClosureMarkedDihedral (inclusion)

def ambientCoordinates : Matrix.GeneralLinearGroup Bool ℂ :=
  Matrix.GeneralLinearGroup.map inclusion (coordinateGL basisB)

def normalize : MulAut (PGL2 ℂ) := MulAut.conj ((pglMk ℂ ambientCoordinates)⁻¹)

def normalized (H : Subgroup (PGL2 ℂ)) : Subgroup (PGL2 ℂ) := H.map normalize.toMonoidHom

theorem normalize_X : normalize xClass = xClass := by
  change (pglMk ℂ ambientCoordinates)⁻¹ * pglMk ℂ xGL *
    pglMk ℂ ambientCoordinates = pglMk ℂ xGL
  rw [← map_inv,← map_mul,← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨1,one_ne_zero,?_⟩
  have hi : ((ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Matrix Bool Bool ℂ) =
      Matrix.map (Matrix.of basisB.inverse) inclusion := rfl
  change (ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ).val * xGL.val * ambientCoordinates.val = _
  rw [hi]
  ext a b
  cases a <;> cases b <;>
    norm_num [ambientCoordinates,coordinateGL,basisB,UB,UBInv,IntermediateField.coe_val,coe_imaginaryUnit,
      Matrix.mul_apply,Fintype.sum_bool,xGL,antidiagonalGL,antidiagonal,
      inclusion,ClosureMarkedDihedral.inclusion,Signature.equality,Signature.disequality] <;>
    ring_nf <;>
    first
    | change (2 : ℂ)⁻¹ - (2 : ℂ)⁻¹ * Complex.I^2 = 1; norm_num [Complex.I_sq]
    | change -(Complex.I^2 * (2 : ℂ)⁻¹) + (2 : ℂ)⁻¹ = 1; norm_num [Complex.I_sq]

theorem normalize_Z : normalize zClass = xClass*zClass := by
  change (pglMk ℂ ambientCoordinates)⁻¹ * pglMk ℂ zGL *
    pglMk ℂ ambientCoordinates = pglMk ℂ xGL * pglMk ℂ zGL
  rw [← map_inv,← map_mul,← map_mul,← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  apply projectiveClass_eq_iff.mpr
  refine ⟨Complex.I,Complex.I_ne_zero,?_⟩
  have hi : ((ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ) : Matrix Bool Bool ℂ) =
      Matrix.map (Matrix.of basisB.inverse) inclusion := rfl
  change (ambientCoordinates⁻¹ : Matrix.GeneralLinearGroup Bool ℂ).val * zGL.val * ambientCoordinates.val = _
  rw [hi]
  ext a b
  cases a <;> cases b <;>
    norm_num [ambientCoordinates,coordinateGL,basisB,UB,UBInv,IntermediateField.coe_val,coe_imaginaryUnit,
      Matrix.mul_apply,Fintype.sum_bool,xGL,antidiagonalGL,antidiagonal,zGL,diagonalGL,diagonal,
      inclusion,ClosureMarkedDihedral.inclusion,Signature.equality,Signature.disequality] <;>
    ring_nf <;>
    first
    | change Complex.I^2 * (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 0; norm_num [Complex.I_sq]
    | change -(Complex.I * (2 : ℂ)⁻¹ * 2) = -Complex.I; ring
    | change (2 : ℂ)⁻¹ * Complex.I * 2 = Complex.I; ring
    | change -(2 : ℂ)⁻¹ - (2 : ℂ)⁻¹ * Complex.I^2 = 0; norm_num [Complex.I_sq]

theorem normalize_Y : normalize (xClass*zClass) = zClass := by
  rw [map_mul,normalize_X,normalize_Z,← mul_assoc]
  have hx : xClass*xClass=1 := by simpa only [pow_two] using xClass_square
  rw [hx,one_mul]

/-- The native-Y branch itself supplies the marked normalization. -/
theorem normalized_centralizer (H : Subgroup (PGL2 ℂ))
    (hH : H ≤ Subgroup.centralizer ({xClass*zClass} : Set (PGL2 ℂ))) :
    normalized H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  rintro q ⟨r,hr,rfl⟩
  have hc : Commute r (xClass*zClass) := Subgroup.mem_centralizer_singleton_iff.mp (hH hr)
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := (hc.map normalize.toMonoidHom).eq
  change normalize r * normalize (xClass*zClass) = normalize (xClass*zClass) * normalize r at h
  rwa [normalize_Y] at h

structure NativeB (H : Subgroup (PGL2 ℂ)) where
  selected : ClosureMarkedDihedral.NativeM (normalized H)

def nativeB (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ Subgroup.centralizer ({xClass*zClass} : Set (PGL2 ℂ)))
    (hx : xClass ∈ H) (h2 : Nat.card H ≠ 2) (h4 : Nat.card H ≠ 4) : NativeB H := by
  let e := H.equivMapOfInjective normalize.toMonoidHom normalize.injective
  letI : Finite (normalized H) := Finite.of_equiv H e.toEquiv
  have hc : Nat.card (normalized H) = Nat.card H := Nat.card_congr e.toEquiv.symm
  have hx' : xClass ∈ normalized H := ⟨xClass,hx,normalize_X⟩
  exact ⟨ClosureMarkedDihedral.nativeM _ (normalized_centralizer H hH) hx'
    (hc ▸ h2) (hc ▸ h4)⟩

namespace NativeB
variable {H : Subgroup (PGL2 ℂ)} (N : NativeB H)
def parameters : Parameters N.selected.m := .B N.selected.range

theorem same_edge : sectorEdge N.parameters.basis = scale (-2*imaginaryUnit) Signature.equality := edgeB

theorem same_reversal (B : Holant.Marked.Mat) :
    transport N.parameters.basis (Kernel.transpose B) = Kernel.transpose (transport N.parameters.basis B) :=
  transport_reversal _ B

end NativeB

namespace Source
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]

def nativeB (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hI : (⟨2,binarySignature (Signature.equality : Binary (K:=L))⟩ : AnySignature L) ∈ F)
    (hY : group φ F hτ ≤ Subgroup.centralizer ({xClass*zClass} : Set (PGL2 ℂ)))
    (h2 : Nat.card (group φ F hτ) ≠ 2) (h4 : Nat.card (group φ F hτ) ≠ 4) :
    NativeB (group φ F hτ) := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  exact ClosureMarkedDihedralB.nativeB _ hY (nativeX_mem φ F hτ hI) h2 h4

/-- Forward dictionary for EVERY actual ordered source binary in this
constructed B branch. The actual source table is kept before transport. -/
theorem actual_sector_spectrum (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : NativeB (group φ F hτ)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    sectorTransfer basisB (Matrix.map B φ) ∈ groupM N.selected.m :=
  ClosureMarkedDihedralCoordinates.Source.actual_sector_spectrum basisB φ F hτ N.selected B hB

theorem actual_transformed_monomial (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : NativeB (group φ F hτ)) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    IsMonomial (transport basisB (Matrix.map B φ)) :=
  N.parameters.actual_isMonomial _ _ (actual_sector_spectrum φ F hτ N B hB) (ProjectivelyEqual.refl _)

/-- Inverse FULL ordered phase coverage for row consumers. The raw actual
representative remains over L and retains its original key/tree access; only
its analytically transported table occurs on the normal-form side. -/
theorem standard_source_representative (φ : L →+* Scalar) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) (N : NativeB (group φ F hτ))
    (p : Bool) (t : Scalar) (ht : Roots N.selected.m t) :
    ∃ j : completeGroup F hτ, ∃ c : Scalar, c ≠ 0 ∧
      transport basisB (Matrix.map (actualRepresentative F hτ j) φ) =
        scale c (ClosureMarkedDihedral.standard p t) := by
  obtain ⟨j,c,hc,he⟩ := ClosureMarkedDihedralCoordinates.Source.source_sector_representative
    basisB φ F hτ N.selected p t ht
  refine ⟨j,c*(imaginaryUnit/2),mul_ne_zero hc (div_ne_zero imaginaryUnit_ne_zero (by norm_num)),?_⟩
  rw [transport_eq_transfer,he,edgeInverseB,scale_mul,Kernel.mul_equality]

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralB
end
