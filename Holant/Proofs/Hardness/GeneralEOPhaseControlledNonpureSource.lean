import Holant.Proofs.Hardness.GeneralEOPhaseControlledSource
import Holant.Proofs.Hardness.GeneralEONonpureHardness

/-! Final common-sign nonpure negative EO source with its full length control.
Nonpurity supplies the non-ARS row internally. Every branch produces an actual
programme with runtime, query-length, and storage evidence over the unchanged
original family, without a caller-supplied pinning or hardness backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledNonpureSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace C
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard)
end C
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (sign : EOSign)
variable (he : ∀i,Signature.CentralSupport (G i))
variable (hs : ∀i,EONegativeWitness.Supports sign (EONegativePairReduction.signature G i))
variable (negative : ¬EOTract (preprocess (EONegativePairReduction.family G)))
variable (j : Fin s) (hp : ¬GeneralEODEQProducer.Pure sign (G j))
local instance : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

include hp in
/-- The selected nonpure row alone supplies the controlled source split. -/
theorem selected_pinning_or_hardness
    (hE : Signature.CentralSupport (G j))
    (hS : EONegativeWitness.Supports sign ⟨a j.val,G j⟩) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ C.ControlledCountingHard G :=
  GeneralEOPhaseControlledSource.selected_pinning_or_hardness G j hE
    (GeneralEONonpurePinning.nonpure_nonars (G j) sign hE hS hp)

include he hs negative hp in
/-- No projection to an ordinary reduction occurs at either terminal branch. -/
theorem countingHard : C.ControlledCountingHard G := by
  rcases selected_pinning_or_hardness G sign j hp (he j) (hs j) with h | h
  · intro α ea f w
    exact ⟨GeneralEONonpureHardness.originalSource G sign he hs negative j hp (Classical.choice h) w⟩
  · exact h

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- The actual final original-family programme, with all resource guarantees. -/
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  Classical.choice (countingHard G sign he hs negative j hp α ea count w)

variable (nonpure : ¬∀i,GeneralEODEQProducer.Pure sign (G i))

include he hs negative nonpure in
/-- The nonpure original label is selected internally and control is retained. -/
theorem exists_nonpure_countingHard : C.ControlledCountingHard G := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp nonpure
  exact countingHard G sign he hs negative i hi

/-- A caller need only supply nonpurity of the family, not a selected label. -/
def source_of_nonpure (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  Classical.choice (exists_nonpure_countingHard G sign he hs negative nonpure α ea count w)


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledNonpureSource
