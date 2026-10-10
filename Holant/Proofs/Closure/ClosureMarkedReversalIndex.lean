import Holant.Proofs.Closure.ClosureMarkedReversalOvergroup

/-! The actual complete group is NORMAL and has index at most two in the
constructed semantic mark extension. The source and ambient statements use
the same actual group and the same semantic overgroup, without adding Z to
any gadget alphabet. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversalIndex
open Holant
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosureMarkedReversal ClosureMarkedReversalOvergroup
variable {L : Type*} [Field L]

theorem overgroup_le_normalizer (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    semanticOvergroup F hτ ≤ Subgroup.normalizer (completeGroup F hτ : Set (PGL2 L)) := by
  rw [semantic_generated,Subgroup.closure_le]
  intro q hq
  rcases hq with he | hq
  · rw [he]
    exact completeGroup_normalizedZ F hτ
  · exact (completeGroup F hτ).le_normalizer hq

/-- This normality is derived from actual reversal, not a model hypothesis. -/
theorem actual_normal (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    ((completeGroup F hτ).subgroupOf (semanticOvergroup F hτ)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (actual_le F hτ)).mpr
    (overgroup_le_normalizer F hτ)

theorem actual_index_le_two (F : SignatureFamily L) (hτ : ResidualTorsion F)
    [Finite (completeGroup F hτ)] :
    ((completeGroup F hτ).subgroupOf (semanticOvergroup F hτ)).index ≤ 2 := by
  letI := semantic_finite F hτ
  let S := (completeGroup F hτ).subgroupOf (semanticOvergroup F hτ)
  have hs : Nat.card S = Nat.card (completeGroup F hτ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (actual_le F hτ)).toEquiv
  have hm := S.index_mul_card
  rw [hs] at hm
  have hc := semantic_cardinal F hτ
  rw [← hm] at hc
  exact Nat.le_of_mul_le_mul_right hc Nat.card_pos

namespace Ambient
open Holant.Tractable Holant.Marked
open Holant.LocalDrafts.MainChain.RingHomRealization
open ClosureMarkedDihedral.Source
open ClosureMarkedReversalOvergroup.Ambient
variable [NumberField L]

theorem actual_normal (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    ((group φ F hτ).subgroupOf (overgroup φ F hτ)).Normal :=
  ClosureMarkedReversalIndex.actual_normal _ _

theorem actual_index_le_two (φ : L →+* Scalar) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    ((group φ F hτ).subgroupOf (overgroup φ F hτ)).index ≤ 2 := by
  letI := ClosureFieldBridgeGroups.actualFiniteGroup (complexEmbedding φ) F hτ
  exact ClosureMarkedReversalIndex.actual_index_le_two _ _

end Ambient
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversalIndex
end
