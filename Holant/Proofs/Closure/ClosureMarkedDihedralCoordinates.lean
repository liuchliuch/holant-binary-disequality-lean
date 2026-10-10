import Holant.Proofs.Closure.ClosureMarkedCyclic

/-! Exact algebraic coordinate transport for actual ORIGINAL-field transfer
representatives. Coordinate matrices are not gadget resources. Every selected
actual key remains in the original complete group, with a nonzero algebraic
sector-coordinate scalar and exact ordered transfer identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralCoordinates
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosureMarkedCyclic (coordinateGL)
open ClosureMarkedDihedral (inclusion)

def ambientCoordinates (U : InvertibleKernel) : Matrix.GeneralLinearGroup Bool ℂ :=
  Matrix.GeneralLinearGroup.map inclusion (coordinateGL U)

def normalize (U : InvertibleKernel) : MulAut (PGL2 ℂ) :=
  MulAut.conj ((pglMk ℂ (ambientCoordinates U))⁻¹)

def normalized (U : InvertibleKernel) (H : Subgroup (PGL2 ℂ)) : Subgroup (PGL2 ℂ) :=
  H.map (normalize U).toMonoidHom

def normalizedGL (U : InvertibleKernel) (V : Matrix.GeneralLinearGroup Bool Scalar) :
    Matrix.GeneralLinearGroup Bool Scalar := (coordinateGL U)⁻¹ * V * coordinateGL U

theorem normalizedGL_class (U : InvertibleKernel) (V : Matrix.GeneralLinearGroup Bool Scalar) :
    pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (normalizedGL U V)) =
      normalize U (pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion V)) := by
  change pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion (normalizedGL U V)) =
    (pglMk ℂ (ambientCoordinates U))⁻¹ *
      pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion V) * pglMk ℂ (ambientCoordinates U)
  simp only [normalizedGL,map_mul,map_inv,ambientCoordinates]

theorem normalizedGL_matrix (U : InvertibleKernel) (V : Matrix.GeneralLinearGroup Bool Scalar) :
    (normalizedGL U V : Binary (K:=Scalar)) = conjugate U.symm (V : Binary (K:=Scalar)) := by
  have hi : ((coordinateGL U)⁻¹ : Matrix.GeneralLinearGroup Bool Scalar).val = Matrix.of U.inverse := rfl
  change ((coordinateGL U)⁻¹ : Matrix.GeneralLinearGroup Bool Scalar).val * V.val *
    (coordinateGL U).val = _
  rw [hi]
  apply Matrix.ext
  intro a b
  simp [coordinateGL,conjugate,InvertibleKernel.symm,Matrix.mul_apply,Fintype.sum_bool,
    Kernel.mul_apply,add_comm,add_left_comm]

namespace Source
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]

def actualTransferGL (F : SignatureFamily L) (B : Binary (K:=L))
    (hB : ActualNonsingular F B) : Matrix.GeneralLinearGroup Bool L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) (by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero hB.2 det_X_ne_zero)

theorem actualTransfer_mem (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) (actualTransferGL F B hB)) ∈
      group φ F hτ :=
  ⟨Matrix.GeneralLinearGroup.map (complexEmbedding φ) (actualTransferGL F B hB),
    ClosureFieldBridgeGroups.actualTransfers_map (complexEmbedding φ)
      ⟨B,hB,1,one_ne_zero,(one_smul L _).symm⟩,rfl⟩

theorem actual_normalized_member (U : InvertibleKernel) (φ : L →+* Scalar)
    (F : SignatureFamily L) (hτ : ResidualTorsion F) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion
      (normalizedGL U (Matrix.GeneralLinearGroup.map φ (actualTransferGL F B hB)))) ∈
        normalized U (group φ F hτ) := by
  rw [normalizedGL_class]
  exact ⟨pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding φ) (actualTransferGL F B hB)),
    actualTransfer_mem φ F hτ B hB,rfl⟩

theorem actual_normalized_matrix (U : InvertibleKernel) (φ : L →+* Scalar)
    (F : SignatureFamily L) (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    (normalizedGL U (Matrix.GeneralLinearGroup.map φ (actualTransferGL F B hB)) : Binary (K:=Scalar)) =
      sectorTransfer U (Matrix.map B φ) := by
  rw [normalizedGL_matrix]
  have he : (Matrix.GeneralLinearGroup.map φ (actualTransferGL F B hB) : Binary (K:=Scalar)) =
      Matrix.of (Kernel.mul (Matrix.map B φ) Signature.disequality) := by
    apply Matrix.ext
    intro a b
    cases a <;> cases b <;>
      simp [actualTransferGL,transfer,Matrix.map_apply,Matrix.mul_apply,X,
        Signature.disequality,Kernel.mul_apply]
  rw [he]
  rfl

theorem actual_sector_spectrum (U : InvertibleKernel) (φ : L →+* Scalar)
    (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : ClosureMarkedDihedral.NativeM (normalized U (group φ F hτ)))
    (B : Binary (K:=L)) (hB : ActualNonsingular F B) :
    sectorTransfer U (Matrix.map B φ) ∈ groupM N.m := by
  have h := N.ordered_transfer _ (actual_normalized_member U φ F hτ B hB)
  rwa [actual_normalized_matrix] at h

/-- Every complete normalized phase selects a real frozen ORIGINAL-field
representative. The coordinate transformation is charged separately; it is
never used as a fictitious source oracle or palette label. -/
theorem source_sector_representative (U : InvertibleKernel) (φ : L →+* Scalar)
    (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (N : ClosureMarkedDihedral.NativeM (normalized U (group φ F hτ)))
    (p : Bool) (t : Scalar) (ht : Roots N.m t) :
    ∃ j : completeGroup F hτ, ∃ c : Scalar, c ≠ 0 ∧
      sectorTransfer U (Matrix.map (actualRepresentative F hτ j) φ) =
        scale c (ClosureMarkedDihedral.standard p t) := by
  have hm : 0 < N.m := by have := N.range; omega
  let V := ClosureMarkedDihedral.phaseGL hm p t ht
  have hv := ClosureMarkedDihedral.phaseClass_mem N p t ht
  obtain ⟨r,hr,he⟩ := hv
  change r ∈ completeGroup (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily
    (complexEmbedding φ) F) (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ) at hr
  rw [ClosureFieldBridgeGroups.completeGroup_image (complexEmbedding φ) F hτ] at hr
  obtain ⟨j,hj,hjmap⟩ := hr
  let key : completeGroup F hτ := ⟨j,hj⟩
  let B := actualRepresentative F hτ key
  have hb := actualRepresentative_actual F hτ key
  let W := actualTransferGL F B hb
  have hj' : pglMk L W = j := by
    apply pglToProjectiveClass_injective
    rw [pglToProjectiveClass_mk]
    exact actualRepresentative_class F hτ key
  have hw : pglMk ℂ (Matrix.GeneralLinearGroup.map inclusion
      (normalizedGL U (Matrix.GeneralLinearGroup.map φ W))) = pglMk ℂ V := by
    rw [normalizedGL_class]
    change normalize U (pglExtend (complexEmbedding φ) (pglMk L W)) = pglMk ℂ V
    rw [hj',hjmap]
    exact he
  have hp := pglMk_eq_iff_projectiveClass_eq.mp hw
  rw [ClosureMarkedDihedral.phaseGL_matrix] at hp
  have hn : (ClosureMarkedDihedral.standard p t : Binary (K:=Scalar)) ≠ 0 := by
    cases p
    · exact ClosureMarkedDihedral.R_ne_zero t
    · exact ClosureMarkedDihedral.S_ne_zero t
  have hs := projectiveClass_map_injective inclusion hn hp
  obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp hs
  refine ⟨key,c,hc,?_⟩
  rw [← actual_normalized_matrix U φ F B hb]
  exact he

end Source
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralCoordinates
end
