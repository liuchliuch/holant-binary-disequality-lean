import Holant.Proofs.Hardness.GeneralEOSkewPhaseExtraction
import Holant.Proofs.Hardness.GeneralEOSelfdualPhaseSource

/-! Remove the supplied-signed-cap hypothesis from the entire common
complement-sign sector. Antiselfdual sources produce their own physical cap;
selfdual sources use the accepted signed-square oracle removal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSkewPhaseSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace S
export GeneralEOPhaseExtractionSource (Pinning CountingHard inclusion)
end S
namespace C
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard pinning_or_controlled_hardness)
end C
namespace E
export GeneralEOSkewPhaseExtraction (Skew original_signed_binary)
end E
set_option backward.isDefEq.respectTransparency false
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

theorem nonzero_of_nonars (f : Signature ℂ n)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale f) : ∃x,f x≠0 := by
  classical
  by_contra hz
  push Not at hz
  apply hA
  refine ⟨1,one_ne_zero,fun _ => 0,?_,?_⟩
  · intro x
    simp
  · funext x
    simpa using hz x

/-- Actual original-label antiselfdual source exit with a length-controlled
hardness programme. No signed binary is supplied by the caller. -/
theorem antiselfdual_pinning_or_controlled_hardness
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hS : E.Skew (T.map S.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    S.Pinning G ∨ C.ControlledCountingHard G := by
  obtain ⟨B,BL,t,hBL,hBN,ht,hBt⟩ := E.original_signed_binary G S.inclusion
    T TL hL hN hE hS (nonzero_of_nonars _ hA)
  exact C.pinning_or_controlled_hardness G B BL hBL hBN t ht hBt
    T TL hL hN hE (Or.inr hS) hA

/-- Cap-free source theorem for both complement-sign sectors, with the
literal pin-elimination and counting-hardness interfaces over G. -/
theorem pinning_or_hardness
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hS : GeneralEOPhaseExtractionSigns.Sign (T.map S.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G := by
  rcases hS with hS|hS
  · exact GeneralEOSelfdualPhaseSource.pinning_or_hardness G T TL hL hN hE hS hA
  · rcases antiselfdual_pinning_or_controlled_hardness G T TL hL hN hE hS hA with hp|hh
    · exact Or.inl (GeneralEOSelfdualPhaseSource.elimination_of_pinning G hp)
    · right
      intro α ea f w
      obtain ⟨r⟩ := hh α ea f w
      exact ⟨r.reduction⟩


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSkewPhaseSource
