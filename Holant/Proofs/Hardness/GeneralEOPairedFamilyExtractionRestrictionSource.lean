import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionRestrictionValue
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionOriginal

/-! The fixed-minor compiler is a length-controlled source into exactly the
reserved-pin oracle, then into the original family and original field codec.
There is no supplied pin, arbitrary gadget realization or hardness premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRestrictionSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
namespace V
export GeneralEOPairedFamilyExtractionRestrictionValue
  (minor query_valid query_value rejected_invalid validatedQuery validatedComputes)
end V
namespace N
export GeneralEOPairedFamilyExtractionPinSource (coefficients value controlled)
end N
namespace C
export GeneralEOPairedCSPFamilyFieldClosed (pairing covers)
end C
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed leftLabel rightLabel extracted)
end E
namespace T
export GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s m : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)
variable (q : Fin ((P left).count+(P right).count) → Bool ⊕ Fin m)

local instance : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

def coefficient : Signature (GeneralEOPairedCSPField.field G) m :=
  V.minor P left right q (N.coefficients G P)

def value (r : GeneralEOPairedCSPRaw.Raw) : GeneralEOPairedCSPField.field G :=
  if r.WellFormed m then GeneralEOPairedFamilyExtractionWriter.rawValue (coefficient G P left right q) r else 0

theorem query_value (r : GeneralEOPairedCSPRaw.Raw) :
    value G P left right q r=N.value G P (V.validatedQuery P left right q r) := by
  by_cases hr : r.WellFormed m
  · simp only [value,hr,ite_true,V.validatedQuery,N.value,V.query_valid P left right q r hr]
    exact (V.query_value P left right q (N.coefficients G P) r).symm
  · simp only [value,hr,ite_false,V.validatedQuery,N.value,V.rejected_invalid P]

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (GeneralEOPairedCSPFamilyRaw.encoding s) (A.presentation G).encoding
      (value G P left right q) (N.value G P) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (V.validatedComputes P left right q) (identityComputes (A.presentation G).encoding)
    (N.controlled G P hf).sourceOutputBound (value G P left right q)
    (query_value G P left right q)

variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

abbrev chosenLeft := E.leftLabel G he hn hc ha
abbrev chosenRight := E.rightLabel G he hn hc hp

variable (p : Fin ((C.pairing G he hn hc (chosenLeft G he hn hc ha)).count+
    (C.pairing G he hn hc (chosenRight G he hn hc hp)).count) → Bool ⊕ Fin m)

abbrev selectedValue := value G (C.pairing G he hn hc)
  (chosenLeft G he hn hc ha) (chosenRight G he hn hc hp) p

theorem coefficient_exact (z : Fin m → Bool) :
    (coefficient G (C.pairing G he hn hc)
      (chosenLeft G he hn hc ha) (chosenRight G he hn hc hp) p z : AlgebraicComplex)=
        E.extracted G he hn hc ha hp (T.substitute p z) := rfl

/-- The target is literally the unchanged originalG family and its original
presentation, via the accepted internal support pairing and pin elimination. -/
def originalSource :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (selectedValue G he hn hc ha hp p) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (controlled G (C.pairing G he hn hc)
      (chosenLeft G he hn hc ha) (chosenRight G he hn hc hp) p (C.covers G he hn hc))
    (GeneralEOPairedFamilyExtractionOriginal.pinSource G he hn hc)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionRestrictionSource
