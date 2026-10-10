import Holant.Proofs.Closure.ClosureMarkedMatrixFacts
import Holant.Marked.Reversal
import Mathlib.Tactic.Group
import Holant.Proofs.FiniteGroups.Stabilization.FrozenDeck

/-! Universal actual marked invariant. Native-X ordered gadgets are closed
under port reversal. Their COMPLETE actual transfer subgroup is normalized
by literal Z, through the exact determinant-weighted two-by-two identity.
Z is a semantic coordinate mark; no Z gadget, palette label or oracle is added.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversal
open Holant
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {L : Type*} [Field L]

/-- The same actual source gadget with only its two boundary ports exchanged. -/
theorem actual_transpose {F : SignatureFamily L} {B : Binary (K:=L)}
    (hB : ActualNonsingular F B) : ActualNonsingular F B.transpose := by
  refine ⟨?_,?_⟩
  · exact realizes_orientBinary hB.1 true
  · simpa only [Matrix.det_transpose] using hB.2

theorem actualTransfers_reversal (F : SignatureFamily L) : ReversalStable (actualTransfers F) := by
  rintro T ⟨B,hB,c,hc,rfl⟩
  refine ⟨B.transpose,actual_transpose hB,c,hc,?_⟩
  simp only [reverseTransfer,Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,
    transfer_transpose,reverseTransfer]

/-- Exact determinant-weighted relation. Ordinary transpose and the native X
edge occur literally; neither projective scalar nor port order is discarded. -/
theorem reverse_determinant (U : Matrix.GeneralLinearGroup Bool L) :
    reverseTransfer (U : Binary (K:=L)) =
      Matrix.det (U : Binary (K:=L)) •
        (nativeZGL * U⁻¹ * nativeZGL : Matrix.GeneralLinearGroup Bool L).val := by
  let V := nativeZGL * U * nativeZGL
  let W := nativeZGL * U⁻¹ * nativeZGL
  have hzw : nativeZGL * nativeZGL = (1 : Matrix.GeneralLinearGroup Bool L) := by
    simpa only [pow_two] using (nativeZGL_square (L:=L))
  have hvw : (V : Binary (K:=L)) * (W : Binary (K:=L)) = 1 := by
    change (V * W : Matrix.GeneralLinearGroup Bool L).val = _
    have he : V * W = 1 := by
      dsimp [V,W]
      calc
        _ = (nativeZGL * U) * (nativeZGL * nativeZGL) * (U⁻¹ * nativeZGL) := by group
        _ = 1 := by rw [hzw]; simp [mul_assoc,hzw]
    exact congrArg Units.val he
  have hp : reverseTransfer (U : Binary (K:=L)) * (V : Binary (K:=L)) =
      Matrix.det (U : Binary (K:=L)) • (1 : Binary (K:=L)) := by
    rw [det_bool]
    ext a b
    cases a <;> cases b <;>
      simp [reverseTransfer,V,nativeZGL,nativeZ,X,Matrix.mul_apply,Matrix.one_apply,
        Signature.disequality,Matrix.transpose_apply] <;> ring
  calc
    reverseTransfer (U : Binary (K:=L)) =
        reverseTransfer (U : Binary (K:=L)) * ((V : Binary (K:=L)) * (W : Binary (K:=L))) := by
      rw [hvw,Matrix.mul_one]
    _ = (reverseTransfer (U : Binary (K:=L)) * (V : Binary (K:=L))) * (W : Binary (K:=L)) :=
      (Matrix.mul_assoc _ _ _).symm
    _ = Matrix.det (U : Binary (K:=L)) • (W : Binary (K:=L)) := by
      rw [hp,Matrix.smul_mul,Matrix.one_mul]

/-- Reversal is nonsingular, with the same native-edge factors. -/
def reverseGL (U : Matrix.GeneralLinearGroup Bool L) : Matrix.GeneralLinearGroup Bool L :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (reverseTransfer (U : Binary (K:=L))) (by
    simp only [reverseTransfer,Matrix.det_mul,Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero det_X_ne_zero U.det_ne_zero) det_X_ne_zero)

theorem reverseClass (U : Matrix.GeneralLinearGroup Bool L) :
    pglMk L (reverseGL U) = nativeZClass * (pglMk L U)⁻¹ * nativeZClass := by
  rw [nativeZClass,← map_inv,← map_mul,← map_mul]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  exact projectiveClass_eq_iff.mpr ⟨Matrix.det (U : Binary (K:=L)),U.det_ne_zero,reverse_determinant U⟩

theorem completeGroup_conjugateZ (F : SignatureFamily L) (hτ : ResidualTorsion F)
    {q : PGL2 L} (hq : q ∈ completeGroup F hτ) :
    nativeZClass * q * nativeZClass ∈ completeGroup F hτ := by
  have hr : ∀ r ∈ completeGroup F hτ,
      nativeZClass * r⁻¹ * nativeZClass ∈ completeGroup F hτ := by
    rintro r ⟨U,hU,rfl⟩
    rw [← reverseClass]
    exact ⟨reverseGL U,actualTransfers_reversal F _ hU,rfl⟩
  simpa only [inv_inv] using hr q⁻¹ ((completeGroup F hτ).inv_mem hq)

/-- Universal actual invariant; no retained Z resource is assumed or added. -/
theorem completeGroup_normalizedZ (F : SignatureFamily L) (hτ : ResidualTorsion F) :
    nativeZClass ∈ Subgroup.normalizer (completeGroup F hτ : Set (PGL2 L)) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  apply Subgroup.ext
  intro q
  constructor
  · rintro ⟨r,hr,rfl⟩
    change nativeZClass * r * nativeZClass⁻¹ ∈ completeGroup F hτ
    rw [nativeZClass_inv]
    exact completeGroup_conjugateZ F hτ hr
  · intro hq
    refine ⟨nativeZClass * q * nativeZClass,completeGroup_conjugateZ F hτ hq,?_⟩
    change nativeZClass * (nativeZClass * q * nativeZClass) * nativeZClass⁻¹ = q
    rw [nativeZClass_inv]
    have hz : (nativeZClass : PGL2 L) * nativeZClass = 1 := by
      simpa only [pow_two] using (nativeZClass_square (L:=L))
    simp [mul_assoc,← mul_assoc nativeZClass nativeZClass,hz]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedReversal
end
