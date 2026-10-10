import Holant.Proofs.Hardness.GeneralEOPairedFamilyBundleSource

/-! The finite signed-minor source ends at literal originalValue G, with the
proved coefficient transport and unchanged original input dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace M
export GeneralEOPairedFamilyBundleSource (signedValue controlled)
end M
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
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s t u : ℕ} {arity a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (Q : (i : Fin u) → OrientedPerfectPairing (a i.val))
variable (label : Fin t → Fin s)
variable (signs : (i : Fin t) → Fin (P (label i)).count → Bool)
variable (recipe : GeneralEOPairedFamilyBundleRaw.Recipe Q
  (GeneralEOPairedFamilySigned.pairing P label signs))
local instance : Algebra ℚ (W.field G) := (W.field G).algebra'
local instance : CharZero (W.field G) := algebraRat.charZero (W.field G)

abbrev value := M.signedValue Q (W.signatures G) P label signs recipe

def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction (GeneralEOPairedCSPFamilyRaw.encoding u) (A.presentation G).encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
      (value G P Q label signs recipe) (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (M.controlled (A.presentation G) Q (W.signatures G) P label signs recipe
      (fun i => W.covers G i (P i) (hf i))) (A.targetTransport G)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleOriginal
