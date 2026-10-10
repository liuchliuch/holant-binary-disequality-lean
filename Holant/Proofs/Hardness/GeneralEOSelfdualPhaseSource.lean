import Holant.Proofs.Hardness.GeneralEOSignedTensorRemovalSource
import Holant.Proofs.Hardness.GeneralEOAugmentedPinField
import Holant.Proofs.Hardness.GeneralEOAugmentedPhaseSource
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSelfdualAlternative

/-! Unconditional selfdual non-ARS source exit. A signed tensor square removes
the literal signed label as an oracle programme. Literal pin inclusion and
field-codec transport pull both augmented-family exits back to the original
family; a signed binary gadget over the original family is never assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSelfdualPhaseSource
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
export GeneralEOPhaseExtractionSource (Pinning CountingHard inclusion)
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

/-- Identifies the two already literal unbounded-pin source interfaces. -/
theorem elimination_of_pinning (h : P.Pinning G) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) := by
  obtain ⟨r⟩ := h
  rw [GeneralEOAffineNetworkOriginalSource.literal_source_value] at r
  refine ⟨?_⟩
  apply GeneralEOCentralHoleHardnessPinning.samePalette G (GeneralEOPinnedDescentPalette.pinned G)
    rfl (fun _ => rfl)
  rw [GeneralEOSinglePinPaletteBridge.literal_family]
  exact r

theorem signed_cap : GeneralEOPhaseExtractionNetwork.Signed
    ((A.cap (D.signed (K:=AlgebraicComplex))).map P.inclusion) 1 := by
  unfold GeneralEOPhaseExtractionNetwork.Signed
  simp only [Network.denote_map,A.cap,Network.denote_corolla,D.signed]
  norm_num

variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hNL : LabelledNetwork.Exact G N NL) (hNN : ∀e,N.edge e=Signature.disequality)
variable (e : Equiv.Perm (Fin 4)) (c : AlgebraicComplex) (hc : c≠0)
variable (hv : Tensor.reindex e N.denote=
  EOBinaryPlaneCore.lift (GeneralEOPhaseExtractionSelfdualQuaternary.product c true))

include hNL hNN hc hv in
theorem pull_pinning (h : P.Pinning (augmented G)) : P.Pinning G := by
  obtain ⟨r⟩ := h
  exact ⟨C.composeControlled (F.source G (D.signed (K:=AlgebraicComplex)))
    (C.composeControlled r (D.source G N NL hNL hNN e c hc hv))⟩

include hNL hNN hc hv in
theorem pull_hardness
    (h : GeneralEOPhaseExtractionControlledSource.ControlledCountingHard (augmented G)) :
    P.CountingHard G := by
  intro α ea f w
  obtain ⟨r⟩ := h α ea f w
  exact ⟨(C.composeControlled r (D.source G N NL hNL hNN e c hc hv)).reduction⟩

include hNL hNN hc hv in
/-- Consumes the actual signed-square witness while retaining the original
source graph and both independent generated-field answer codecs. -/
theorem signed_square_exit (S : Network AlgebraicComplex n) (SL : Labelling S.shape s 1 a)
    (hL : LabelledNetwork.Exact G S SL) (hN : ∀i,S.edge i=Signature.disequality)
    (hE : Signature.CentralSupport S.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign (S.map P.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (S.map P.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ P.CountingHard G := by
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
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ P.CountingHard G := by
  rcases GeneralEOPhaseExtractionSelfdualAlternative.pinning_hardness_or_signed_square
    G S SL hL hN hE hS hA with hp|hh|⟨Q,QL,e,c,hQL,hQN,hc,hv⟩
  · exact Or.inl hp
  · exact Or.inr hh
  · exact signed_square_exit G Q QL hQL hQN e c hc hv S SL hL hN hE (Or.inl hS) hA

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSelfdualPhaseSource
