import Holant.Proofs.Closure.ClosureMarkedDihedralA0

/-! NEW POST-RECOVERY SOURCE; fresh strict verification is required.
The A^0 branch's ACTUAL Y edge-switch source. Native Z class membership
is descended into the unchanged original field; its frozen representative is
an actual binary c·ZX with c a nonzero ORIGINAL-field scalar. The literal
coordinate mark Z itself is not asserted to be a binary gadget or palette label.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralA0Resources
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open ClosureMarkedDihedral.Source
open ClosureMarkedReversal
variable {L : Type*} [Field L] [NumberField L]

theorem source_mark_map (φ : L →+* Scalar) :
    pglExtend (complexEmbedding φ) (nativeZClass (L:=L)) = zClass := by
  rw [nativeZClass,pglExtend_mk]
  apply congrArg (pglMk ℂ)
  apply Units.ext
  ext a b
  cases a <;> cases b <;>
    simp [nativeZGL,nativeZ,zGL,diagonalGL,diagonal]

theorem source_mark_actual (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hZ : zClass ∈ group φ F hτ) : nativeZClass ∈ completeGroup F hτ := by
  change zClass ∈ completeGroup (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily
    (complexEmbedding φ) F) (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding φ) F hτ) at hZ
  rw [ClosureFieldBridgeGroups.completeGroup_image (complexEmbedding φ) F hτ] at hZ
  obtain ⟨q,hq,he⟩ := hZ
  have hs : q = nativeZClass := pglExtend_injective (complexEmbedding φ)
    (he.trans (source_mark_map φ).symm)
  exact hs ▸ hq

def sourceKey (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hZ : zClass ∈ group φ F hτ) : completeGroup F hτ :=
  ⟨nativeZClass,source_mark_actual φ F hτ hZ⟩

def nativeY : Binary (K:=L) := nativeZ * X

theorem source_Y_actual_scalar (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hZ : zClass ∈ group φ F hτ) :
    ∃ c : L, c ≠ 0 ∧ actualRepresentative F hτ (sourceKey φ F hτ hZ) = c • nativeY := by
  have h := actualRepresentative_class F hτ (sourceKey φ F hτ hZ)
  change projectiveClass (transfer (actualRepresentative F hτ (sourceKey φ F hτ hZ))) =
    pglToProjectiveClass (nativeZClass (L:=L)) at h
  rw [nativeZClass,pglToProjectiveClass_mk] at h
  obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp h
  refine ⟨c,hc,?_⟩
  have hb := congrArg (fun M : Binary (K:=L) => M*X) he
  simpa only [transfer,Matrix.mul_assoc,X_mul_X,Matrix.mul_one,Matrix.smul_mul,nativeY,
    nativeZGL] using hb

theorem nativeY_map (φ : L →+* Scalar) : Matrix.map (nativeY (L:=L)) φ = Holant.Marked.Y := by
  apply Matrix.ext
  intro a b
  cases a <;> cases b <;>
    simp [nativeY,nativeZ,X,Holant.Marked.Y,Holant.Marked.Z,Matrix.map_apply,
      Matrix.mul_apply,Kernel.mul_apply,diagonalKernel,Signature.disequality]

/-- The actual source binary, its nonzero scalar and both ordered entries
are kept. Constructing its retained tree/programme is the ordinary charged
actual-representative factory, not a coordinate-matrix oracle. -/
theorem source_Y_mapped_scalar (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hZ : zClass ∈ group φ F hτ) :
    ∃ c : L, c ≠ 0 ∧ Matrix.map (actualRepresentative F hτ (sourceKey φ F hτ hZ)) φ =
      scale (φ c) Holant.Marked.Y := by
  obtain ⟨c,hc,he⟩ := source_Y_actual_scalar φ F hτ hZ
  refine ⟨c,hc,?_⟩
  rw [he,Matrix.map_smul' φ c _ φ.map_mul,nativeY_map]
  rfl

/-- A concrete original-field resource receipt. The actual frozen binary is
kept literally c·Y; this does not relabel the coordinate matrix Y as an oracle. -/
structure YResource (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hZ : zClass ∈ group φ F hτ) where
  coefficient : L
  coefficient_nonzero : coefficient ≠ 0
  literal : actualRepresentative F hτ (sourceKey φ F hτ hZ) = coefficient • nativeY
  actual : ActualNonsingular F (actualRepresentative F hτ (sourceKey φ F hτ hZ))
  mapped_literal : Matrix.map (actualRepresentative F hτ (sourceKey φ F hτ hZ)) φ =
    scale (φ coefficient) Holant.Marked.Y

def sourceY (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (hZ : zClass ∈ group φ F hτ) : YResource φ F hτ hZ := by
  let receipt := source_Y_actual_scalar φ F hτ hZ
  let c := Classical.choose receipt
  have hc := (Classical.choose_spec receipt).1
  have he := (Classical.choose_spec receipt).2
  refine ⟨c,hc,he,actualRepresentative_actual F hτ (sourceKey φ F hτ hZ),?_⟩
  rw [he,Matrix.map_smul' φ c _ φ.map_mul,nativeY_map]
  rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedDihedralA0Resources
end
