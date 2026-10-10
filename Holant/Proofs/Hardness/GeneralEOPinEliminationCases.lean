import Holant.Proofs.Hardness.GeneralEOAffinePlaneOriginalConsumers
import Holant.Proofs.Hardness.GeneralEOZeroSidedCapConsumers
import Holant.Proofs.Hardness.GeneralEONonARSPinningConsumers

/-! Three proved original-family pin suppliers, joined at one literal source
and target interface. Applicability is a sufficient condition, not a claimed
characterization of non-ARS families. Fixed-family choice is not a polynomial
algorithm for recognizing or synthesizing a supplier from a family encoding. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinEliminationCases
open Holant Holant.Tractable Holant.Complexity Computability
namespace F
export GeneralEONonARSPinningFiniteCap (Applicable)
end F
namespace Z
export GeneralEOZeroSidedCapSource (Applicable)
end Z
namespace A
export GeneralEOAffinePlaneOriginalField (ambient)
end A
namespace P
export GeneralEOPinnedDescentPalette (presentation pinnedValue)
end P
namespace E
export GeneralEOCentralHoleHardnessPinning (pinnedEncoding targetEncoding)
end E
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalValue)
end O
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

/-- Literal original coefficient and port data; no gadget or hardness premise. -/
structure AffineWitness where
  label : Fin s
  row : Signature AlgebraicComplex 4
  slot : (⟨a label.val,G label⟩ : AnySignature AlgebraicComplex)=⟨4,row⟩
  ports : Equiv.Perm (Fin 4)
  plane : Tensor.reindex ports row=EOBinaryPlaneCore.lift (A.ambient row ports)
  full : EOBinaryPlaneClassification.Full (A.ambient row ports)
  affine : Affine (A.ambient row ports)
  nonproduct : ¬Product (A.ambient row ports)

def Applicable : Prop := F.Applicable G ∨ Z.Applicable G ∨ Nonempty (AffineWitness G)

abbrev Elimination := LengthControlledOracleReduction
  (E.pinnedEncoding (s:=s) (a:=a)) (P.presentation G).encoding
  (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding
  (P.pinnedValue G) (O.originalValue G)

def affineElimination (w : AffineWitness G) : Elimination G :=
  GeneralEOAffinePlaneOriginalConsumers.elimination G w.label w.row w.slot w.ports
    w.plane w.full w.affine w.nonproduct

/-- Each fixed branch is an already proved real Boolean-stack programme. -/
def elimination (h : Applicable G) : Elimination G := by
  classical
  by_cases hf : F.Applicable G
  · exact GeneralEONonARSPinningConsumers.selectedElimination G hf
  by_cases hz : Z.Applicable G
  · exact GeneralEOZeroSidedCapConsumers.selectedElimination G hz
  exact affineElimination G (Classical.choice ((h.resolve_left hf).resolve_left hz))

/-- Rejection is recorded honestly as three remaining supplier failures. -/
theorem rejected_iff : ¬Applicable G ↔
    ¬F.Applicable G ∧ ¬Z.Applicable G ∧ ¬Nonempty (AffineWitness G) := by
  simp only [Applicable,not_or]

variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}
def source (h : Applicable G) (D : GeneralEONegativeSupportSource.Source G)
    (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (E.targetEncoding (s:=s) (a:=a)) (P.presentation G).encoding f (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (GeneralEOSupportHoleSource.source G D w) (elimination G h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinEliminationCases
