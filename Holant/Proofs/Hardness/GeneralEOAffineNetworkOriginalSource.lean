import Holant.Proofs.Hardness.GeneralEOAffineNetworkField
import Holant.Proofs.Hardness.GeneralEOAffineNetworkPinSource

/-! An actual original-labelled native-X quaternary network whose compressed
opposite-pair plane is full, affine and nonproduct supplies unrestricted 01
pin elimination to the unchanged original family, field and presentation.
There is no matrix-power, field-extension, oracle or hardness assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkOriginalSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open FixedGadgetSubstitution UniversalPairReduction
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace F
export GeneralEOAffineNetworkField
  (lifted labels binary ambient scale original_plane scale_nonzero power)
end F
namespace D
export GeneralEOAffineNetworkDEQSource (G targetEncoding)
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

variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀i,N.edge i=Signature.disequality)
variable (e : Equiv.Perm (Fin 4))
variable (hplane : Tensor.reindex e N.denote=EOBinaryPlaneCore.lift (F.ambient N e))
variable (hf : EOBinaryPlaneClassification.Full (F.ambient N e))
variable (hA : Affine (F.ambient N e)) (hP : ¬Product (F.ambient N e))

theorem original_labels :
    LabelledNetwork.Exact (D.G (presentation G) (tables G))
      (F.lifted G N NL) (F.labels G N NL) := by
  change LabelledNetwork.Exact (ValueJoins.signatures (presentation G) (tables G)) _ _
  rw [GeneralEOSinglePinSource.decoded_original]
  exact GeneralEONonARSPinningFieldBridge.exact G N NL

/-- The complete literal original-G-plus01 to original-G machine. The
24-copy scalar identity is derived internally in the original field. -/
def source : LengthControlledOracleReduction
    (P.inputEncoding (s:=s) (a:=a)) (presentation G).encoding
    (D.targetEncoding (s:=s) (a:=a)) (presentation G).encoding
    (sourceValue G) (O.originalValue G) :=
  GeneralEOAffineNetworkPinSource.source (presentation G) (tables G)
    (F.lifted G N NL) (F.labels G N NL) e (F.scale G N NL e)
    (F.scale_nonzero G N NL hN hn e hf) (GeneralEOSinglePinSource.native_tables G)
    (original_labels G N NL) (GeneralEONonARSPinningFieldBridge.native G N NL)
    (F.binary G N NL e) (F.original_plane G N NL hN hn e hplane)
    (F.power G N NL hN hn e hf hA hP)

/-- Source semantics are exactly arbitrary many literal directed01 pins. -/
theorem literal_source_value : sourceValue G=
    GeneralEOSinglePinAmplificationSemantics.value (GeneralEOBinaryPinSource.original G) := by
  unfold sourceValue GeneralEOSinglePinAmplificationProgramme.sourceValue
  change GeneralEOSinglePinAmplificationSemantics.value
    (ValueJoins.signatures (presentation G) (tables G))=_
  rw [GeneralEOSinglePinSource.decoded_original]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffineNetworkOriginalSource
