import Holant.Proofs.Hardness.GeneralEOBinarySignedHardness
import Holant.Proofs.Hardness.GeneralEOPairedFamilyGadgetOriginal
import Holant.Proofs.Hardness.GeneralEOClosedCriterion

/-! Universal closed-support finite-family negative EO source. The bad binary,
private-variable gadget, signed native compiler, pin elimination, field maps
and final original-G oracle are all internally constructed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOClosedHardness
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace U
export GeneralEOPairedFamilyExtractionUniversalSource (coefficient coefficient_failures)
end U
namespace E
export GeneralEOPairedFamilyExtractionChoice (compressed)
end E
namespace W
export GeneralEOPairedCSPField (field)
end W
namespace A
export GeneralEOPairedCSPOriginalField (presentation)
end A
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))
local instance : Algebra ℚ (W.field G) := (W.field G).algebra'
variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

attribute [local irreducible] GeneralEOBinarySignedHardness.source
  GeneralEOPairedFamilyGadgetOriginal.selectedControlled

/-- The full reduction retains original ordered labels and original answer
codec, with actual polynomial query, runtime and storage control. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  C.composeControlled
    (GeneralEOBinarySignedHardness.source (W.field G) (A.presentation G)
      (U.coefficient G he hn hc ha hp) (U.coefficient_failures G he hn hc ha hp).1
      (U.coefficient_failures G he hn hc ha hp).2 w)
    (GeneralEOPairedFamilyGadgetOriginal.selectedControlled G he hn hc ha hp)

include he hn hc ha hp in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  intro α ea f w
  exact ⟨(source G he hn hc ha hp w).reduction⟩

variable (negative : ¬EOTract (preprocess (EONegativePairReduction.family G)))

def negativeSource (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  source G he hn hc (GeneralEOClosedCriterion.closed_negative_failures G he hn hc negative).1
    (GeneralEOClosedCriterion.closed_negative_failures G he hn hc negative).2 w

include he hn hc negative in
theorem negative_countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  intro α ea f w
  exact ⟨(negativeSource G he hn hc negative w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool → Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 arity) (O.originalPresentation G).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj)) (O.originalValue G) :=
  negativeSource G he hn hc negative (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOClosedHardness
