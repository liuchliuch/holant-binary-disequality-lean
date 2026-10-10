import Holant.Proofs.Hardness.GeneralEODEQProducerNormalize
import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryPinning
import Holant.Proofs.Hardness.GeneralEOARSSupport
import Holant.Proofs.Hardness.GeneralEOSupportHoleSource

/-! An actual unpinned DEQ4 graph supplies the existing full pin-elimination
programme, preserving original coefficients and answer encoding. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQUnpinnedElimination
open Computability Holant Holant.Tractable Holant.Complexity
namespace D
export GeneralEODEQProducerNormalize (Produced)
end D
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
namespace S
export GeneralEOPhaseExtractionSource (inclusion)
end S
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

def eliminate (Q : D.Produced G) : GeneralEOPinEliminationCases.Elimination G :=
  GeneralOddHigherResidueQuaternaryPinning.deqElimination G Q.network Q.labels
    Q.exact Q.native Q.scalar Q.nonzero Q.denote

variable (Q : D.Produced G) (j : Fin s)
variable (he : Signature.CentralSupport (G j))
variable (ha : GeneralEOARSBoundary.ARSUpToScale (fun x => S.inclusion (G j x)))
variable (hc : ¬GeneralEONegativeClosedSupport.Closed (G j))
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- The two opposite support failures are internally derived from ARS and
nonclosed support, then the actual pin eliminator removes all pins. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (GeneralEOSupportHoleSource.fromFailures G j j he he
      (GeneralEOARSSupport.ars_nonclosed_failures (G j) ha hc).1
      (GeneralEOARSSupport.ars_nonclosed_failures (G j) ha hc).2 w)
    (eliminate G Q)

include Q j he ha hc in
theorem controlled_hard : GeneralEOPhaseExtractionControlledSource.ControlledCountingHard G := by
  intro α ea f w
  exact ⟨source G Q j he ha hc w⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQUnpinnedElimination
