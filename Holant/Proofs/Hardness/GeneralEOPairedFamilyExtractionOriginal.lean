import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSource
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinSource
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! Literal original-field endpoints for generic mixed-family tensor extraction
and universal compressed-CSP reference pin elimination. Both are actual compiled
length-controlled reductions. Neither asserts an unproved counting backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionOriginal
open Computability Holant Holant.Tractable Holant.Complexity
namespace T
export GeneralEOPairedFamilyExtractionSource (extractedControlled extractedValue)
end T
namespace N
export GeneralEOPairedFamilyExtractionPinSource (value controlled)
end N
namespace C
export GeneralEOPairedCSPFamilyFieldClosed (pairing covers)
end C
namespace F
export GeneralEOPairedCSPFamilyOriginal (closedControlled)
end F
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))

/-- Generic pin elimination, with every support pairing derived internally. -/
def pinSource :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding s) (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (N.value G (C.pairing G he hn hc)) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (N.controlled G (C.pairing G he hn hc) (C.covers G he hn hc))
    (F.closedControlled G he hn hc)

variable (ha : ¬∀i,Affine ((C.pairing G he hn hc i).restrict (G i)))
variable (hp : ¬∀i,Product ((C.pairing G he hn hc i).restrict (G i)))

/-- Internally extract both class failures, expand every tensor row into its
actual labels, then compose the accepted original-field programme. -/
def tensorSource :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (T.extractedValue G he hn hc ha hp) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (T.extractedControlled G he hn hc ha hp) (F.closedControlled G he hn hc)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionOriginal
