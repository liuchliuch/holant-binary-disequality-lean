import Holant.Proofs.Hardness.GeneralEOPairedFamilySigned

/-! The signed compressed-family compiler ends at precisely the original G
oracle and its original coordinate presentation, using the proved rational
answer adapter rather than identifying generated fields or their encodings. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilySignedOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace S
export GeneralEOPairedFamilySigned (value pinnedValue controlled pinnedControlled)
end S
namespace W
export GeneralEOPairedCSPField (field signatures covers)
end W
namespace A
export GeneralEOPairedCSPOriginalField (presentation targetTransport)
end A
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s t : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (label : Fin t → Fin s)
variable (signs : (i : Fin t) → Fin (P (label i)).count → Bool)

local instance : Algebra ℚ (W.field G) := (W.field G).algebra'
local instance : CharZero (W.field G) := algebraRat.charZero (W.field G)

abbrev value := S.value (W.signatures G) P label signs
abbrev pinnedValue := S.pinnedValue (W.signatures G) P label signs

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding t) (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (value G P label signs) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (S.controlled (A.presentation G) (W.signatures G) P label signs
      (fun i => W.covers G i (P i) (hf i))) (A.targetTransport G)

def pinnedControlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding t) (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (pinnedValue G P label signs) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (S.pinnedControlled (A.presentation G) (W.signatures G) P label signs
      (fun i => W.covers G i (P i) (hf i))) (A.targetTransport G)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilySignedOriginal
