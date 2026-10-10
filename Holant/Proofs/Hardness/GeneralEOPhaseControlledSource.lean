import Holant.Proofs.Hardness.GeneralEOPhaseControlledSelfdualSource
import Holant.Proofs.Hardness.GeneralEORootNormSource

/-! Length-controlled version of the completed universal non-ARS source exit.
All phase, norm, and binary-sign mathematics is reused unchanged. The wrapper
retains each actual programme instead of projecting away its length control. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace S
export GeneralEOPhaseExtractionSource (inclusion)
export GeneralEOPhaseExtractionControlledSource (ControlledCountingHard)
end S
namespace B
export GeneralEOPhaseExtractionFieldBridge (family)
end B
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
variable {s n : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- Both common complement-sign branches preserve the full controlled source.
Neither an auxiliary cap nor an oracle hardness premise is supplied. -/
theorem sign_pinning_or_hardness
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hS : GeneralEOPhaseExtractionSigns.Sign (T.map S.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.ControlledCountingHard G := by
  rcases hS with hS | hS
  · exact GeneralEOPhaseControlledSelfdualSource.pinning_or_hardness G T TL hL hN hE hS hA
  · rcases GeneralEOSkewPhaseSource.antiselfdual_pinning_or_controlled_hardness
      G T TL hL hN hE hS hA with hp | hh
    · exact Or.inl (GeneralEOSelfdualPhaseSource.elimination_of_pinning G hp)
    · exact Or.inr hh

/-- The accepted binary-square rigidity proof supplies the mathematical sign. -/
theorem binary_pinning_or_hardness (h : GeneralEOBinarySignSource.BinarySquare G)
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.ControlledCountingHard G :=
  sign_pinning_or_hardness G T TL hL hN hE
    (GeneralEOBinarySignSource.sign G h T TL hL hN hE) hA

/-- Universal source exit: no phase, sign, pin, or hardness assumption remains.
The target is the unchanged original family and its original answer codec. -/
theorem pinning_or_hardness (T : Network AlgebraicComplex n)
    (TL : Labelling T.shape s 1 a) (hL : LabelledNetwork.Exact G T TL)
    (hN : ∀e,T.edge e=Signature.disequality) (hE : Signature.CentralSupport T.denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.ControlledCountingHard G := by
  classical
  by_cases pins : Nonempty (GeneralEOPinEliminationCases.Elimination G)
  · exact Or.inl pins
  exact binary_pinning_or_hardness G
    (GeneralEORootNormSource.binary_square_of_nonars_no_elimination G pins T TL hL hN hE hA)
    T TL hL hN hE hA

theorem selected_pinning_or_hardness (i : Fin s)
    (hE : Signature.CentralSupport (G i))
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (B.family G S.inclusion i)) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.ControlledCountingHard G := by
  apply pinning_or_hardness G (Network.corolla (G i)) (LabelledNetwork.corolla G i)
    (fun _ => rfl) (fun e => Fin.elim0 e)
  · simpa only [Network.denote_corolla] using hE
  · have he : ((Network.corolla (G i)).map S.inclusion).denote =
        B.family G S.inclusion i := by
      funext x
      rw [Network.denote_map,Network.denote_corolla]
      rfl
    rwa [he]

/-- The full family alternative retains genuine ARS as its terminal branch. -/
theorem family_outcome (hE : ∀i,Signature.CentralSupport (G i)) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.ControlledCountingHard G ∨
      GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion) := by
  classical
  by_cases hA : GeneralEOARSBoundary.FamilyARS (B.family G S.inclusion)
  · exact Or.inr (Or.inr hA)
  change ¬∀i,GeneralEOARSBoundary.ARSUpToScale (B.family G S.inclusion i) at hA
  push Not at hA
  obtain ⟨i,hi⟩ := hA
  rcases selected_pinning_or_hardness G i (hE i) hi with hp | hh
  · exact Or.inl hp
  · exact Or.inr (Or.inl hh)


end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseControlledSource
