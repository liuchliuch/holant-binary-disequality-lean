import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralPreserver
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicCards

/-! Every current I/opposite-I coefficient test uses an original actual
representative, with its nonzero multiplier and both native wires retained.
The complete actual dictionary is fixed by the proved current marking. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Cards
open Holant.Certificates
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open GlobalCloseCompletionPlatonicCards (coefficientCard coefficientCard_scale mapped_card)

local notation "NX" => (Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix)

theorem direction_X (opposite : Bool) : Dictionary.direction opposite NX := by
  cases opposite
  · exact GlobalCloseCompletionPlatonicCards.x_direction .icosahedral
  · exact OppositeIcosahedral.direction_X

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (opposite : Bool) (literal : group phi F torsion=Dictionary.group opposite)

include literal in
theorem actual_direction (B : Matrix Bool Bool L) (actual : ActualNonsingular F B) :
    Dictionary.direction opposite (B.map (complexEmbedding phi)) := by
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
  exact (Dictionary.right_X opposite A).mp ((Dictionary.matrix_iff opposite V).mp hv)

include literal in
theorem kernel_alignment (K : ComplexMatrix) (member : Dictionary.direction opposite K) :
    ∃ j : completeGroup F torsion, ∃ c : ℂ, c≠0 ∧
      (actualRepresentative F torsion j).map (complexEmbedding phi)=c • nativePair K := by
  have hd := Preserver.Completion.direction_mul opposite (direction_X opposite) member
  let V := Matrix.GeneralLinearGroup.mkOfDetNeZero (NX*K)
    (Preserver.Completion.direction_det_ne_zero opposite hd)
  have hv : pglMk ℂ V∈group phi F torsion := by
    rw [literal]
    exact (Dictionary.matrix_iff opposite V).mpr hd
  exact GlobalCloseCompletionPlatonicRepresentatives.representative_for_transfer
    phi F torsion V hv

def LiteralDeck (opposite : Bool) (q : Signature ℂ 4) : Prop :=
  ∀ e K, Dictionary.direction opposite K →
    coefficientCard q e K=0 ∨ Dictionary.direction opposite (coefficientCard q e K)

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (model : group (ClosureSourceRows.embedding G) P.family tau=Dictionary.group opposite)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family tau q,MatchingOrZero (actualTransfers P.family) f)

include model core same stable in
theorem current_literal_deck : LiteralDeck opposite
    (RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q) := by
  intro e K member
  obtain ⟨j,c,hc,he⟩ := kernel_alignment (ClosureSourceRows.embedding G) P.family tau opposite model K member
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
    have safe := actual_direction (ClosureSourceRows.embedding G) P.family tau opposite model _ actual
    rw [hcard] at safe
    have unscaled := Dictionary.scale opposite safe (inv_ne_zero hc)
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using unscaled

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.Cards
end
