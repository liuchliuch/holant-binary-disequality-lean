import Holant.Proofs.Hardness.GeneralEOSinglePinSource
import Holant.Proofs.Hardness.GeneralEOPinnedDescentPalette

/-! The one-pin source is exactly the existing original-field literal 01
palette, on unchanged raw input bytes. This bridge exposes the source to the
previously accepted original-labelled descent compilers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinPaletteBridge
open Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open UniversalPairReduction
namespace P
export GeneralEOPinnedDescentPalette (arity original pinned pinnedTables pinnedValue)
end P
namespace S
export GeneralEOSinglePinSource (sourceValue programme_value original)
end S
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature)
end OT
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

private theorem cast_apply {K : Type} [Field K] {m n : ℕ} (h : m=n)
    (f : Signature K m) (x : Fin n → Bool) :
    OT.castSignature h f x=f (fun i => x (Fin.cast h i)) := by
  subst n
  rfl

theorem literal_family : P.pinned G=BinaryFamily.signatures (S.original G) BinaryTable.delta := by
  funext i x
  unfold P.pinned GeneralEOPinnedDescentPalette.palette BinaryFamily.signatures
  split_ifs
  · rw [cast_apply]
    rfl
  · rw [cast_apply]
    rfl

theorem literal_value (r : Input s a) :
    S.sourceValue G r=P.pinnedValue G (forget s a r) := by
  rw [S.programme_value]
  rw [GeneralEOPinnedDescentPalette.pinnedValue,GeneralEOPinnedDescentAccess.targetValue,
    ExactSignatureTables.evaluate_eq_decoded]
  simp only [GeneralEOPinnedDescentAccess.tables,LinearEquiv.apply_symm_apply]
  rw [literal_family]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSinglePinPaletteBridge
