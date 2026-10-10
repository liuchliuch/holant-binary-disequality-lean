import Holant.Proofs.Hardness.GeneralEOSignedTensorRemovalSource
import Holant.Proofs.Hardness.GeneralEOAugmentedPinField
import Holant.Proofs.Hardness.GeneralEOAugmentedPhaseSource
import Holant.Proofs.Hardness.GeneralEOPhaseControlledSelfdualAlternative
import Holant.Proofs.Hardness.GeneralEOSelfdualPhaseSource

/-! Unconditional length-controlled selfdual non-ARS source exit. A signed tensor square removes
the literal signed label as an oracle programme. Literal pin inclusion and
field-codec transport pull both augmented-family exits back to the original
family; a signed binary gadget over the original family is never assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledSelfdualSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace A
export GeneralEOAugmentedPhaseSource (augmented alternative cap)
end A
namespace F
export GeneralEOAugmentedPinField (source)
end F
namespace P
export GeneralEOPhaseExtractionSource (Pinning inclusion)
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard)
end P
namespace D
export GeneralEOSignedTensorRemovalSource (signed source)
end D
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
abbrev augmented := A.augmented G (D.signed (K:=AlgebraicComplex))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
local instance augmentedAlgebra : Algebra ℚ (O.originalField (augmented G)) :=
  (O.originalField (augmented G)).algebra'

export GeneralEOSelfdualPhaseSource (elimination_of_pinning signed_cap)

variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hNL : LabelledNetwork.Exact G N NL) (hNN : ∀e,N.edge e=Signature.disequality)
variable (e : Equiv.Perm (Fin 4)) (c : AlgebraicComplex) (hc : c≠0)
variable (hv : Tensor.reindex e N.denote=
  EOBinaryPlaneCore.lift (GeneralEOPhaseExtractionSelfdualQuaternary.product c true))

export GeneralEOSelfdualPhaseSource (pull_pinning)

include hNL hNN hc hv in
theorem pull_hardness
    (h : GeneralEOPhaseExtractionControlledSource.ControlledCountingHard (augmented G)) :
    P.ControlledCountingHard G := by
  intro α ea f w
  obtain ⟨r⟩ := h α ea f w
  exact ⟨C.composeControlled r (D.source G N NL hNL hNN e c hc hv)⟩

include hNL hNN hc hv in
/-- Consumes the actual signed-square witness while retaining the original
source graph and both independent generated-field answer codecs. -/
theorem signed_square_exit (S : Network AlgebraicComplex n) (SL : Labelling S.shape s 1 a)
    (hL : LabelledNetwork.Exact G S SL) (hN : ∀i,S.edge i=Signature.disequality)
    (hE : Signature.CentralSupport S.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign (S.map P.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (S.map P.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ P.ControlledCountingHard G := by
  rcases A.alternative G (D.signed (K:=AlgebraicComplex)) S SL signed_cap hL hN hE hSign hA with hp|hh
  · exact Or.inl (elimination_of_pinning G (pull_pinning G N NL hNL hNN e c hc hv hp))
  · exact Or.inr (pull_hardness G N NL hNL hNN e c hc hv hh)

/-- The selfdual non-ARS residual now has an unconditional original-family
pin-elimination or counting-hardness exit, at arbitrary source arity. -/
theorem pinning_or_hardness (S : Network AlgebraicComplex n) (SL : Labelling S.shape s 1 a)
    (hL : LabelledNetwork.Exact G S SL) (hN : ∀i,S.edge i=Signature.disequality)
    (hE : Signature.CentralSupport S.denote)
    (hS : SelfDualPinObstruction.SelfDual (S.map P.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (S.map P.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ P.ControlledCountingHard G := by
  rcases GeneralEOPhaseControlledSelfdualAlternative.pinning_hardness_or_signed_square
    G S SL hL hN hE hS hA with hp|hh|⟨Q,QL,e,c,hQL,hQN,hc,hv⟩
  · exact Or.inl hp
  · exact Or.inr hh
  · exact signed_square_exit G Q QL hQL hQN e c hc hv S SL hL hN hE (Or.inl hS) hA

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledSelfdualSource
