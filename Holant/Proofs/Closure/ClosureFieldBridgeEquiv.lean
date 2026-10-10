import Holant.Proofs.Closure.ClosureMarkedDihedral

/-! NEW_POST_RECOVERY, pending fresh strict check. The exact actual complete
ambient-group image supplies a group equivalence and reflects cyclicity. This
lets genuine ambient small-group guards be consumed in the unchanged original
field; it creates no new gadget, state compiler or classification assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFieldBridgeEquiv
open Holant Holant.Tractable
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L]

def completeGroupEquiv (phi : L →+* ℂ) (F : SignatureFamily L) (torsion : ResidualTorsion F) :
    completeGroup F torsion ≃*
      completeGroup (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily phi F)
        (ClosureFieldBridgeGroups.mappedTorsion phi F torsion) := by
  rw [ClosureFieldBridgeGroups.completeGroup_image phi F torsion]
  exact (completeGroup F torsion).equivMapOfInjective (pglExtend phi) (pglExtend_injective phi)

theorem completeGroup_isCyclic_iff (phi : L →+* ℂ) (F : SignatureFamily L)
    (torsion : ResidualTorsion F) :
    IsCyclic (completeGroup F torsion) ↔
      IsCyclic (completeGroup (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily phi F)
        (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)) := by
  let e := completeGroupEquiv phi F torsion
  constructor
  · intro hc
    letI : IsCyclic (completeGroup F torsion) := hc
    exact isCyclic_of_surjective e e.surjective
  · intro hc
    letI : IsCyclic (completeGroup (Holant.LocalDrafts.MainChain.RingHomRealization.mapFamily phi F)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)) := hc
    exact isCyclic_of_surjective e.symm e.symm.surjective

variable [NumberField L]

theorem source_isCyclic_iff (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L)
    (torsion : ResidualTorsion F) : IsCyclic (completeGroup F torsion) ↔ IsCyclic (group phi F torsion) :=
  completeGroup_isCyclic_iff (complexEmbedding phi) F torsion

theorem source_not_isCyclic (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L)
    (torsion : ResidualTorsion F) (noncyclic : ¬ IsCyclic (group phi F torsion)) :
    ¬ IsCyclic (completeGroup F torsion) :=
  fun hc => noncyclic ((source_isCyclic_iff phi F torsion).mp hc)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFieldBridgeEquiv
end
