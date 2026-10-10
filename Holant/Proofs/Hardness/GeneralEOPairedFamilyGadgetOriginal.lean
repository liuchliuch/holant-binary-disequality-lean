import Holant.Proofs.Hardness.GeneralEOPairedFamilyGadgetNative
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionUniversalSource

/-! The exact signed singleton-binary palette of the internally selected
private-variable gadget reduces to literal originalValue G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace N
export GeneralEOPairedFamilyGadgetNative (size binary nativeValue controlled)
end N
namespace W
export GeneralEOPairedCSPField (field signatures covers)
end W
namespace A
export GeneralEOPairedCSPOriginalField (presentation targetTransport)
end A
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
namespace D
export GeneralEOPairedFamilyExtractionGadget (Gadget)
end D
namespace U
export GeneralEOPairedFamilyExtractionUniversalSource (gadget coefficient)
end U
namespace C
export GeneralEOPairedCSPFamilyFieldClosed (pairing covers)
end C
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed leftLabel rightLabel)
end E
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)
variable (g : D.Gadget ((P left).count+(P right).count) 2)
local instance : Algebra ℚ (W.field G) := (W.field G).algebra'
local instance : CharZero (W.field G) := algebraRat.charZero (W.field G)

abbrev value := N.nativeValue (N.binary (W.signatures G) P left right g)

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding N.size) (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (value G P left right g) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (N.controlled (W.signatures G) P left right g (A.presentation G)
      (fun i => W.covers G i (P i) (hf i))) (A.targetTransport G)

variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

/-- The coefficient is exactly the previously constructed hard binary, in KG. -/
theorem binary_selected :
    N.binary (W.signatures G) (C.pairing G he hn hc)
      (E.leftLabel G he hn hc ha) (E.rightLabel G he hn hc hp) (U.gadget G he hn hc ha hp) =
      U.coefficient G he hn hc ha hp := by
  rfl

/-- Final signed gadget adapter, matching the native parser's literal palette. -/
def selectedControlled :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding N.size) (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (N.nativeValue (U.coefficient G he hn hc ha hp)) (O.originalValue G) := by
  have h := controlled G (C.pairing G he hn hc) (E.leftLabel G he hn hc ha)
    (E.rightLabel G he hn hc hp) (U.gadget G he hn hc ha hp) (C.covers G he hn hc)
  unfold value at h
  rw [binary_selected] at h
  exact h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyGadgetOriginal
