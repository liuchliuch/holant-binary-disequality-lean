import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionChoice
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionWriter
import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyOriginal

/-! The universally extracted disjoint tensor has a real length-controlled
CSP reduction to the literal original family oracle. All pairings and labels
are chosen internally from the actual common-class failures. The remaining
counting-hardness theorem for a single arbitrary-arity compressed tensor is
not assumed or asserted here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
namespace E
export GeneralEOPairedFamilyExtractionChoice
  (compressed leftLabel rightLabel extracted extracted_nonzero extracted_closed extracted_failures)
end E
namespace W
export GeneralEOPairedFamilyExtractionWriter (tensor rawValue query queryComputes query_value wellFormed_iff)
end W
namespace F
export GeneralEOPairedCSPFamilyOriginal (value totalControlled closedControlled)
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
set_option maxHeartbeats 2000000
set_option Elab.async false

variable {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))
variable (P : (i : Fin s) → OrientedPerfectPairing (arity i.val))
variable (left right : Fin s)

local instance : Algebra ℚ (GeneralEOPairedCSPField.field G) :=
  (GeneralEOPairedCSPField.field G).algebra'

/-- Both factors are coefficients in the existing original-family working
field, with its existing presentation; no new tensor field is invented. -/
def coefficient := W.tensor
  (GeneralEOPairedCSPCycles.compress (P left) (GeneralEOPairedCSPField.signatures G left))
  (GeneralEOPairedCSPCycles.compress (P right) (GeneralEOPairedCSPField.signatures G right))

def value (r : GeneralEOPairedCSPRaw.Raw) : GeneralEOPairedCSPField.field G :=
  if r.WellFormed ((P left).count+(P right).count) then
    W.rawValue (coefficient G P left right) r else 0

theorem query_value (r : GeneralEOPairedCSPRaw.Raw) :
    value G P left right r=F.value G P (W.query left right r) := by
  change (if r.WellFormed ((P left).count+(P right).count) then
    W.rawValue (coefficient G P left right) r else 0) =
      (if (W.query left right r).WellFormed P then
        GeneralEOPairedCSPFamilyRaw.value P
          (fun i => GeneralEOPairedCSPCycles.compress (P i) (GeneralEOPairedCSPField.signatures G i))
          (W.query left right r) else 0)
  simp only [W.wellFormed_iff]
  congr 1
  exact (W.query_value P left right
    (fun i => GeneralEOPairedCSPCycles.compress (P i) (GeneralEOPairedCSPField.signatures G i)) r).symm

/-- Actual single-query row expansion to the demanded compressed-family value
and codec. Cover is only used for the already accepted output-length bound. -/
def controlled (hf : ∀i,GeneralEOPairedCSPCycles.Covers (P i) (G i)) :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (GeneralEOPairedCSPFamilyRaw.encoding s) (A.presentation G).encoding
      (value G P left right) (F.value G P) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq
    (W.queryComputes left right) (identityComputes (A.presentation G).encoding)
    (F.totalControlled G P hf).sourceOutputBound (value G P left right)
    (query_value G P left right)

variable (he : ∀i,Signature.CentralSupport (G i)) (hn : ∀i,G i≠0)
variable (hc : ∀i,GeneralEONegativeClosedSupport.Closed (G i))
variable (ha : ¬∀i,Affine (E.compressed G he hn hc i))
variable (hp : ¬∀i,Product (E.compressed G he hn hc i))

abbrev pairing := GeneralEOPairedCSPFamilyFieldClosed.pairing G he hn hc
abbrev chosenLeft := E.leftLabel G he hn hc ha
abbrev chosenRight := E.rightLabel G he hn hc hp
abbrev extractedValue := value G (pairing G he hn hc)
  (chosenLeft G he hn hc ha) (chosenRight G he hn hc hp)

theorem coefficient_exact (x : Fin ((pairing G he hn hc (chosenLeft G he hn hc ha)).count+
    (pairing G he hn hc (chosenRight G he hn hc hp)).count) → Bool) :
    (coefficient G (pairing G he hn hc)
      (chosenLeft G he hn hc ha) (chosenRight G he hn hc hp) x : AlgebraicComplex)=
        E.extracted G he hn hc ha hp x := by
  simp only [coefficient, W.tensor, Tensor.reindex, Tensor.tensor,
    GeneralEOPairedCSPCycles.compress, E.extracted,
    GeneralEOPairedFamilyExtractionTensor.tensor, E.compressed, OrientedPerfectPairing.restrict]
  rfl

/-- Universal family-to-singleton extraction has no caller-chosen row, pin,
triangle, reduction, answer presentation, or pairing. -/
def extractedControlled :
    LengthControlledOracleReduction GeneralEOPairedCSPRaw.encoding (A.presentation G).encoding
      (GeneralEOPairedCSPFamilyRaw.encoding s) (A.presentation G).encoding
      (extractedValue G he hn hc ha hp) (F.value G (pairing G he hn hc)) :=
  controlled G (pairing G he hn hc)
    (chosenLeft G he hn hc ha) (chosenRight G he hn hc hp)
    (GeneralEOPairedCSPFamilyFieldClosed.covers G he hn hc)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionSource
