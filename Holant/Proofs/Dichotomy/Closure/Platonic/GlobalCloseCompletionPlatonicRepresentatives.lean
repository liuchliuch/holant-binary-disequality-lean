import Holant.Proofs.Closure.ClosureMarkedPlatonicSubgroup

/-! Exact original-field representatives of a specified actual complex class.
Only a class already in the actual source group is consumed; an analytic
conjugator never becomes a physical binary. The comparison scalar is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicRepresentatives
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)

theorem representative_for_transfer (V : ComplexGL)
    (member : pglMk ℂ V ∈ group phi F torsion) :
    ∃ j : completeGroup F torsion, ∃ c : ℂ, c≠0 ∧
      (actualRepresentative F torsion j).map (complexEmbedding phi)=
        c • ((V : Matrix Bool Bool ℂ)*X) := by
  change pglMk ℂ V ∈ completeGroup
    (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily (complexEmbedding phi) F)
    (ClosureFieldBridgeGroups.mappedTorsion (complexEmbedding phi) F torsion) at member
  rw [ClosureFieldBridgeGroups.completeGroup_image (complexEmbedding phi) F torsion] at member
  obtain ⟨j,hj,he⟩ := member
  let key : completeGroup F torsion := ⟨j,hj⟩
  let B := actualRepresentative F torsion key
  have hb := actualRepresentative_actual F torsion key
  have hd : Matrix.det (transfer B)≠0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero hb.2 det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hd
  have hj' : pglMk L U=j := by
    apply pglToProjectiveClass_injective
    rw [pglToProjectiveClass_mk]
    exact actualRepresentative_class F torsion key
  have hmap : pglMk ℂ (Matrix.GeneralLinearGroup.map (complexEmbedding phi) U)=pglMk ℂ V := by
    rw [←pglExtend_mk,hj']
    exact he
  obtain ⟨c,hc,hcEq⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp hmap)
  refine ⟨key,c,hc,?_⟩
  have h := congrArg (fun M : Matrix Bool Bool ℂ=>M*X) hcEq
  change (transfer B).map (complexEmbedding phi)*X=(c • (V : Matrix Bool Bool ℂ))*X at h
  rw [←ClosureFieldBridgeGroups.transfer_map] at h
  simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicRepresentatives
end
