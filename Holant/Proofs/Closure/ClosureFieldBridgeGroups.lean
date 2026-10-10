import Holant.Proofs.FiniteGroups.Stabilization.FieldExtension
import Holant.Proofs.FiniteGroups.Stabilization.ExactGroupBound
import Holant.Proofs.Tetrahedral.CyclicResource.PhaseProvenance.FrozenSources

/-! Exact actual-group transport to C. Every ambient actual binary is
descended through its same source graph, using the frozen descent theorem.
The full ambient complete group is proved to be the image of the ORIGINAL
field's actual complete group; it is never a supplied completeness assumption.
This is a semantic routing certificate, not a new state/oracle compiler.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFieldBridgeGroups
open Holant Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open RingHomRealization
namespace Provenance
export Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance
  (actual_preimage mapMatrix_det)
end Provenance
variable {L : Type*} [Field L]

theorem map_X (φ : L →+* ℂ) : (X : Binary (K:=L)).map φ = X := by
  ext a b
  cases a <;> cases b <;> simp [Matrix.map_apply, X, Signature.disequality]

theorem transfer_map (φ : L →+* ℂ) (B : Binary (K:=L)) :
    transfer (B.map φ) = (transfer B).map φ := by
  simp only [transfer, Matrix.map_mul, map_X]

theorem actual_map (φ : L →+* ℂ) {F : SignatureFamily L} {B : Binary (K:=L)}
    (hB : ActualNonsingular F B) : ActualNonsingular (mapFamily φ F) (B.map φ) := by
  refine ⟨?_, ?_⟩
  · have h := @RingHomRealization.realizes_map L ℂ
      (inferInstance : Field L).toSemifield.toCommSemiring
      (inferInstance : Field ℂ).toSemifield.toCommSemiring φ F .disequality 2
      (binarySignature B) hB.1
    exact h
  · change Matrix.det
      (Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance.mapMatrix φ B) ≠ 0
    rw [Provenance.mapMatrix_det]
    exact (map_ne_zero φ).mpr hB.2

/-- Exact preimage of an arbitrary ambient actual nonsingular binary.
No assumed coefficient preimage, phase label, source compiler or safe oracle. -/
theorem actual_preimage (φ : L →+* ℂ) {F : SignatureFamily L} {B : Binary (K:=ℂ)}
    (hB : ActualNonsingular (mapFamily φ F) B) :
    ∃ A : Binary (K:=L), ActualNonsingular F A ∧ A.map φ = B := by
  obtain ⟨g, hg, he⟩ := Provenance.actual_preimage φ hB.1
  have hm : (binaryMatrix g).map φ = B := by
    ext a b
    exact congrFun he ![a,b]
  refine ⟨binaryMatrix g, ⟨?_, ?_⟩, hm⟩
  · simpa only [binarySignature_binaryMatrix] using hg
  · intro hz
    have hdet := hB.2
    rw [← hm] at hdet
    change Matrix.det
      (Holant.LocalDrafts.TetrahedralCompletion.CyclicResource.PhaseProvenance.mapMatrix φ
        (binaryMatrix g)) ≠ 0 at hdet
    rw [Provenance.mapMatrix_det, hz, map_zero] at hdet
    exact hdet rfl

def mappedTorsion (φ : L →+* ℂ) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    ResidualTorsion (mapFamily φ F) := by
  intro B hB
  obtain ⟨A, ha, rfl⟩ := actual_preimage φ hB
  rw [transfer_map]
  exact (hτ A ha).map φ

theorem actualTransfers_map (φ : L →+* ℂ) {F : SignatureFamily L}
    {T : Binary (K:=L)} (hT : T ∈ actualTransfers F) :
    T.map φ ∈ actualTransfers (mapFamily φ F) := by
  obtain ⟨B, hb, c, hc, rfl⟩ := hT
  refine ⟨B.map φ, actual_map φ hb, φ c, (map_ne_zero φ).mpr hc, ?_⟩
  rw [Matrix.map_smul' φ c _ φ.map_mul, transfer_map]

/-- Equality of the FULL ambient group, proved from actual source gadgets.
Foreign ambient scalar multiples add no new projective class. -/
theorem completeGroup_image (φ : L →+* ℂ) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) :
    completeGroup (mapFamily φ F) (mappedTorsion φ F hτ) =
      (completeGroup F hτ).map (pglExtend φ) := by
  apply Subgroup.ext
  intro q
  constructor
  · intro hq
    let r : completeGroup (mapFamily φ F) (mappedTorsion φ F hτ) := ⟨q,hq⟩
    obtain ⟨B, hb, hm⟩ := actual_preimage φ
      (actualRepresentative_actual (mapFamily φ F) (mappedTorsion φ F hτ) r)
    have hdet : Matrix.det (transfer B) ≠ 0 := by
      rw [transfer, Matrix.det_mul]
      exact mul_ne_zero hb.2 det_X_ne_zero
    let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) hdet
    have hu : (U : Binary (K:=L)) ∈ actualTransfers F :=
      ⟨B, hb, 1, one_ne_zero, (one_smul L _).symm⟩
    have hsource : pglMk L U ∈ completeGroup F hτ := ⟨U, hu, rfl⟩
    refine ⟨pglMk L U, hsource, ?_⟩
    apply pglToProjectiveClass_injective
    rw [pglExtend_mk, pglToProjectiveClass_mk]
    change projectiveClass ((transfer B).map φ) = pglToProjectiveClass q
    rw [← transfer_map, hm]
    exact actualRepresentative_class (mapFamily φ F) (mappedTorsion φ F hτ) r
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨U, hu, rfl⟩ := hq
    refine ⟨Matrix.GeneralLinearGroup.map φ U, actualTransfers_map φ hu, ?_⟩
    exact (pglExtend_mk φ U).symm

variable [NumberField L]

theorem completeGroup_card (φ : L →+* ℂ) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) :
    Nat.card (completeGroup (mapFamily φ F) (mappedTorsion φ F hτ)) =
      Nat.card (completeGroup F hτ) := by
  rw [completeGroup_image, pglExtend_card]

theorem completeGroup_bound_original (φ : L →+* ℂ) (F : SignatureFamily L)
    (hτ : ResidualTorsion F) :
    Nat.card (completeGroup (mapFamily φ F) (mappedTorsion φ F hτ)) ≤
      sourceGroupBound (Module.finrank ℚ L) := by
  rw [completeGroup_card]
  exact completeGroup_card_le_sourceBound F hτ

/-- The routing group is the actual ambient group, with the source field
and its bound retained. This does not convert L into a new source state. -/
def actualFiniteGroup (φ : L →+* ℂ) (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    Finite (completeGroup (mapFamily φ F) (mappedTorsion φ F hτ)) := by
  rw [completeGroup_image φ F hτ]
  letI := completeGroup_finite F hτ
  exact Finite.of_equiv (completeGroup F hτ)
    ((completeGroup F hτ).equivMapOfInjective (pglExtend φ) (pglExtend_injective φ)).toEquiv

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureFieldBridgeGroups
end
