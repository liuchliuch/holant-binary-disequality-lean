import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralConditions
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMarking
import Holant.Proofs.Dichotomy.Closure.External.GlobalCloseCompletionExternalTetrahedralCurrent

/-! All marked octahedral coefficient tests are mapped original-current raw
cards. Each alignment carries its actual nonzero multiplier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralCards
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source ClosureMarkedReversalOvergroup.Ambient
open scoped BigOperators

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (f : Form) (literal : group phi F torsion=Coordinates.Models.group f)

include literal in
theorem actual_direction (B : Matrix Bool Bool L) (actual : ActualNonsingular F B) :
    Direction f (B.map (complexEmbedding phi)) := by
  let A := B.map (complexEmbedding phi)
  have ha : ActualNonsingular (mapFamily (complexEmbedding phi) F) A :=
    ClosureFieldBridgeGroups.actual_map (complexEmbedding phi) actual
  have hd : (transfer A).det≠0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero ha.2 det_X_ne_zero
  let V := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer A) hd
  have hv : pglMk ℂ V∈group phi F torsion :=
    ⟨V,⟨A,ha,1,one_ne_zero,(one_smul ℂ _).symm⟩,rfl⟩
  rw [literal] at hv
  have hg := (Coordinates.Models.matrix_iff f V).mp hv
  change Direction f (transfer A) at hg
  have hh := direction_mul hg (direction_X f)
  change Direction f ((A*Holant.Certificates.MatchingContractionClosure.X)*
    Holant.Certificates.MatchingContractionClosure.X) at hh
  simpa only [transfer,Matrix.mul_assoc,
    Holant.Certificates.MatchingContractionClosure.X_mul_X,Matrix.mul_one] using hh

include literal in
theorem kernel_alignment (K : ComplexMatrix) (member : Direction f K) :
    ∃ j : completeGroup F torsion, ∃ c : ℂ, c≠0 ∧
      (actualRepresentative F torsion j).map (complexEmbedding phi)=c • nativePair K := by
  have hd := direction_mul (direction_X f) member
  let V := Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix)*K)
    (hd.det_ne_zero)
  have hv : pglMk ℂ V∈group phi F torsion := by
    rw [literal]
    exact (Coordinates.Models.matrix_iff f V).mpr hd
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionPlatonicRepresentatives.representative_for_transfer
    phi F torsion V hv
  exact ⟨j,c,hc,he⟩

export GlobalCloseCompletionPlatonicCards (coefficientCard coefficientCard_scale mapped_card)

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (f : Form)
variable (model : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family tau q,MatchingOrZero (actualTransfers P.family) f)

include model core same stable in
theorem current_literal_deck : Preserver.LiteralDeck f
    (RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q) := by
  intro e K member
  change coefficientCard _ e K=0 ∨ Direction f (coefficientCard _ e K)
  obtain ⟨j,c,hc,he⟩ := kernel_alignment (ClosureSourceRows.embedding G) P.family tau f model K member
  let B := actualRepresentative P.family tau j
  have hb := actualRepresentative_actual P.family tau j
  have hpair : nativePair (B.map (complexEmbedding (ClosureSourceRows.embedding G)))=c • K := by
    rw [he]
    ext a b
    rw [nativePair_apply]
    change c*nativePair K (!a) (!b)=c*K a b
    rw [nativePair_apply,Bool.not_not,Bool.not_not]
  have hcard := mapped_card (complexEmbedding (ClosureSourceRows.embedding G)) q e B
  rw [hpair,coefficientCard_scale] at hcard
  rcases ClosureSourceRows.actualCard_actual_or_zero G P tau q stable core same e B hb with zero|actual
  · left
    have hz : c • coefficientCard (RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q) e K=0 := by
      rw [←hcard,zero]
      ext a b
      simp [binaryMatrix]
    exact (smul_eq_zero.mp hz).resolve_left hc
  · right
    have safe := actual_direction (ClosureSourceRows.embedding G) P.family tau f model _ actual
    rw [hcard] at safe
    have unscaled := safe.smul (inv_ne_zero hc)
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using unscaled


include core same stable in
theorem actual_marked_deck
    (semantic : HasModel (overgroup (ClosureSourceRows.embedding G) P.family tau)
      (.platonic .octahedral)) :
    ∃ f : Form, group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f ∧
      Preserver.LiteralDeck f
        (RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q) := by
  have actual := GlobalCloseCompletionExternalTetrahedralCurrent.platonic_actual_eq_semantic
    G P tau q core same stable .octahedral semantic
  have hz : zClass∈group (ClosureSourceRows.embedding G) P.family tau := by
    rw [actual,←ClosureMarkedReversalOvergroup.Ambient.native_mark]
    exact ClosureMarkedReversalOvergroup.mark_mem _ _
  obtain ⟨f,hf⟩ := Coordinates.Alignment.group_is_marked
    (group (ClosureSourceRows.embedding G) P.family tau)
    (nativeX_mem _ _ _ P.equality) hz (actual.symm ▸ semantic)
  exact ⟨f,hf,current_literal_deck G P tau f hf q core same stable⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralCards
end
