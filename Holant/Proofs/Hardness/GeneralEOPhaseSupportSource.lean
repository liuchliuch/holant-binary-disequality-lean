import Holant.Proofs.Hardness.GeneralEORootNormSource
import Holant.Proofs.Hardness.GeneralEOSupportHoleSource

/-! Root consumers for the actual support-obstruction source. The proved
unrestricted non-ARS split supplies pin elimination internally, and that
machine is composed with the existing pinned hardness programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseSupportSource
open Computability Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace S
export GeneralEOPhaseExtractionSource (inclusion CountingHard)
end S
namespace B
export GeneralEOPhaseExtractionFieldBridge (family)
end B
namespace P
export GeneralEOPinnedDescentPalette (presentation)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalValue originalPresentation)
end O
namespace E
export GeneralEOPinEliminationCases (Elimination)
end E
namespace N
export GeneralEONegativeSupportSource (Source select literal)
end N
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

/-- The actual support-hole writer and actual pin eliminator run in one
controlled machine with precisely the original-G final value and codec. -/
def source (D : N.Source G) (eliminate : E.Elimination G) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool
      (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
      f (O.originalValue G) :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled
    (GeneralEOSupportHoleSource.source G D w) eliminate

theorem countingHard (D : N.Source G) (eliminate : E.Elimination G) : S.CountingHard G := by
  intro α ea f w
  exact ⟨(source G D eliminate w).reduction⟩

theorem support_hard_or_ars (he : ∀ i, Signature.CentralSupport (G i))
    (D : N.Source G) :
    S.CountingHard G ∨ GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion) := by
  rcases GeneralEORootNormSource.family_outcome G he with pins | hard | ars
  · exact Or.inl (countingHard G D (Classical.choice pins))
  · exact Or.inl hard
  · exact Or.inr ars

/-- A non-ARS original family with the actual support obstruction is hard;
no pin supplier, extraction success, or final hardness premise is supplied. -/
theorem nonars_support_hard (he : ∀ i, Signature.CentralSupport (G i))
    (nonars : ¬GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion))
    (D : N.Source G) : S.CountingHard G :=
  (support_hard_or_ars G he D).resolve_right nonars

theorem nonars_failures_hard (he : ∀ i, Signature.CentralSupport (G i))
    (nonars : ¬GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion))
    (i j : Fin s) (positive : ¬EONegativeWitness.Supports .positive ⟨a i.val,G i⟩)
    (negative : ¬EONegativeWitness.Supports .negative ⟨a j.val,G j⟩) : S.CountingHard G :=
  nonars_support_hard G he nonars (N.select G i j (he i) (he j) positive negative)

theorem nonars_centralHole_hard (he : ∀ i, Signature.CentralSupport (G i))
    (nonars : ¬GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion))
    (i : Fin s) (hole : GeneralEONegativeSupportTensor.CentralHole (G i)) : S.CountingHard G := by
  obtain ⟨T,missing,balanced⟩ := hole
  exact nonars_support_hard G he nonars (N.literal G i T (he i) missing balanced)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseSupportSource
