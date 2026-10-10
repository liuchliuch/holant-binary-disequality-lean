import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMarking
import Holant.Proofs.Dichotomy.Closure.External.GlobalCloseCompletionExternalTetrahedralDictionary

/-! Arity-independent actual placement below a semantic O mark.
The actual group is one of the four full O rows, or the fixed external T row.
The latter is kept explicitly at higher arity; no q4 contradiction is reused. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralPlacement
open Holant Holant.Tractable
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
  (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)

theorem same_of_mark (mark : zClass∈group phi F torsion) :
    group phi F torsion=overgroup phi F torsion := by
  apply le_antisymm (ClosureMarkedReversalOvergroup.actual_le _ _)
  intro q hq
  change q∈group phi F torsion ∨ ∃r∈group phi F torsion,
    q=ClosureMarkedReversal.nativeZClass*r at hq
  rw [native_mark] at hq
  rcases hq with hq | ⟨r,hr,rfl⟩
  · exact hq
  · exact (group phi F torsion).mul_mem mark hr

include identity in
theorem actual_cases
    (semantic : HasModel (overgroup phi F torsion) (.platonic .octahedral)) :
    (∃f : Form,group phi F torsion=Coordinates.Models.group f) ∨
      group phi F torsion=GlobalCloseCompletionExternalTetrahedralDictionary.group := by
  have hc : Nat.card (overgroup phi F torsion)≤2*Nat.card (group phi F torsion) := by
    rw [source_cardinal]
    exact cardinal_original phi F torsion
  obtain ⟨p,hp,g,hk,hh⟩ := ClosureMarkedPlatonicSubgroup.actual_model
    (group phi F torsion) (overgroup phi F torsion)
    (ClosureMarkedReversalOvergroup.actual_le _ _) hc .octahedral semantic
  rcases hp with rfl | ⟨_,rfl⟩
  · have same : group phi F torsion=overgroup phi F torsion :=
      Subgroup.map_injective (MulAut.conj g).injective (hh.trans hk.symm)
    have hz : zClass∈group phi F torsion := by
      rw [same,←native_mark]
      exact ClosureMarkedReversalOvergroup.mark_mem _ _
    exact Or.inl (Coordinates.Alignment.group_is_marked _
      (nativeX_mem phi F torsion identity) hz ⟨g,hh⟩)
  · have outside : zClass∉group phi F torsion := by
      intro mark
      have same := same_of_mark phi F torsion mark
      rw [same] at hh
      have bad := congrArg (fun J : Subgroup (PGL2 ℂ)=>Nat.card J) (hh.symm.trans hk)
      rw [modelPGL_card,modelPGL_card] at bad
      norm_num [Holant.Certificates.RainbowOrbit.size] at bad
    exact Or.inr (GlobalCloseCompletionExternalTetrahedralDictionary.current_group
      phi F torsion identity semantic ⟨g,hh⟩ outside)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralPlacement
end
