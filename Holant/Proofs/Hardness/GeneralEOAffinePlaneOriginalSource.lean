import Holant.Proofs.Hardness.GeneralEOAffinePlaneOriginalField
import Holant.Proofs.Hardness.GeneralEOAffinePlaneDEQPinSource

/-! A full affine nonproduct opposite-pair plane in a literal original row
supplies unrestricted directed pins over the original coefficient field and
original answer codec. The temporary E row is eliminated by actual copies of
that same row; its label is retained even when original signatures coincide. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneOriginalSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.FixedGadgetSubstitution Holant.Complexity.UniversalPairReduction
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace F
export GeneralEOAffinePlaneOriginalField
  (row row_slot binary ambient scale original_plane scale_nonzero power)
end F
namespace D
export GeneralEOAffinePlaneDEQSource (G targetEncoding)
end D
namespace P
export GeneralEOSinglePinAmplificationProgramme (Input inputEncoding sourceValue)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
abbrev presentation := O.originalPresentation G
abbrev tables := O.originalTables G
abbrev sourceValue := P.sourceValue (presentation G) (tables G)

variable (j : Fin s) (M : Signature AlgebraicComplex 4)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4))
variable (hplane : Tensor.reindex e M=EOBinaryPlaneCore.lift (F.ambient M e))
variable (hf : EOBinaryPlaneClassification.Full (F.ambient M e))
variable (hA : Affine (F.ambient M e)) (hP : ¬Product (F.ambient M e))

theorem original_slot :
    (⟨a j.val,D.G (presentation G) (tables G) j⟩ : AnySignature (O.originalField G))=
      ⟨4,F.row G j M hj⟩ := by
  change (⟨a j.val,ValueJoins.signatures (presentation G) (tables G) j⟩ : AnySignature (O.originalField G))=_
  rw [GeneralEOSinglePinSource.decoded_original]
  exact F.row_slot G j M hj

/-- Actual length-controlled counting reduction, with no matrix-period
hypothesis remaining in its interface. -/
def source : LengthControlledOracleReduction
    (P.inputEncoding (s:=s) (a:=a)) (presentation G).encoding
    (D.targetEncoding (s:=s) (a:=a)) (presentation G).encoding
    (sourceValue G) (O.originalValue G) :=
  GeneralEOAffinePlaneDEQPinSource.source (presentation G) (tables G) j
    (F.row G j M hj) (original_slot G j M hj) e (F.scale G j M hj e)
    (F.scale_nonzero G j M hj e hf) (GeneralEOSinglePinSource.native_tables G)
    (F.binary G j M hj e) (F.original_plane G j M hj e hplane)
    (F.power G j M hj e hf hA hP)

/-- The source is literally the original family with directed01 appended. -/
theorem literal_source_value : sourceValue G=
    GeneralEOSinglePinAmplificationSemantics.value (GeneralEOBinaryPinSource.original G) := by
  unfold sourceValue GeneralEOSinglePinAmplificationProgramme.sourceValue
  change GeneralEOSinglePinAmplificationSemantics.value
    (ValueJoins.signatures (presentation G) (tables G))=_
  rw [GeneralEOSinglePinSource.decoded_original]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneOriginalSource
