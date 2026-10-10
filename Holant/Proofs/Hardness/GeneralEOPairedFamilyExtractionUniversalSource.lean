import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionUniversal
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPrivateSource

/-! Internally choose the proved binary gadget and compile its arbitrary raw
CSP instances into the original finite family and original answer codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionUniversalSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed extracted extracted_failures)
end E
namespace O
export GeneralEOPairedFamilyExtractionOrigin (extracted_origin extracted_xorClosed)
end O
namespace U
export GeneralEOPairedFamilyExtractionUniversal (exists_gadget)
end U
namespace B
export GeneralEOPairedFamilyExtractionGadget (Gadget denote Bad)
end B
namespace P
export GeneralEOPairedFamilyExtractionPrivateSource (coefficient value originalSource coefficient_exact)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

def gadget := Classical.choose (U.exists_gadget (E.extracted G he hn hc ha hp)
  (O.extracted_origin G he hn hc ha hp) (O.extracted_xorClosed G he hn hc ha hp)
  (E.extracted_failures G he hn hc ha hp).1 (E.extracted_failures G he hn hc ha hp).2)

theorem gadget_bad : B.Bad (E.extracted G he hn hc ha hp) (gadget G he hn hc ha hp) :=
  Classical.choose_spec (U.exists_gadget (E.extracted G he hn hc ha hp)
    (O.extracted_origin G he hn hc ha hp) (O.extracted_xorClosed G he hn hc ha hp)
    (E.extracted_failures G he hn hc ha hp).1 (E.extracted_failures G he hn hc ha hp).2)

def coefficient : Signature (GeneralEOPairedCSPField.field G) 2 :=
  P.coefficient 2 (gadget G he hn hc ha hp).privateCount G he hn hc ha hp
    (gadget G he hn hc ha hp).ports

def complexCoefficient : Signature AlgebraicComplex 2 :=
  fun z => (coefficient G he hn hc ha hp z : AlgebraicComplex)

attribute [local irreducible] gadget GeneralEOPairedFamilyExtractionChoice.extracted
  GeneralEOPairedFamilyExtractionBundleSource.coefficient

theorem coefficient_eq : complexCoefficient G he hn hc ha hp =
    B.denote (E.extracted G he hn hc ha hp) (gadget G he hn hc ha hp) := by
  funext z
  exact P.coefficient_exact 2 (gadget G he hn hc ha hp).privateCount G he hn hc ha hp
    (gadget G he hn hc ha hp).ports z

theorem coefficient_failures : ¬Affine (complexCoefficient G he hn hc ha hp) ∧
    ¬Product (complexCoefficient G he hn hc ha hp) := by
  rw [coefficient_eq]
  exact gadget_bad G he hn hc ha hp

abbrev value := P.value 2 (gadget G he hn hc ha hp).privateCount G he hn hc ha hp
  (gadget G he hn hc ha hp).ports

/-- All gadget variables and finite original labels are internally selected.
This is a real controlled source; a separate binary counting-hardness bridge
must consume it before claiming original-family hardness. -/
def originalSource : LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding
    (GeneralEOPairedCSPOriginalField.presentation G).encoding
    (RawClosedNetwork.validatedEncoding s 1 arity)
    (Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget.originalPresentation G).encoding
    (value G he hn hc ha hp)
    (Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget.originalValue G) :=
  P.originalSource 2 (gadget G he hn hc ha hp).privateCount G he hn hc ha hp
    (gadget G he hn hc ha hp).ports

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionUniversalSource
