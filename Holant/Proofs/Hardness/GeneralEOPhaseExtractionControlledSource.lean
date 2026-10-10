import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSource

/-! Preserve the actual length-controlled hardness constructors of the
conditional phase source, so the result can be composed with oracle removal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionControlledSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace F
export GeneralEOPhaseExtractionFieldBridge (nonars_quaternary)
end F
namespace Q
export GeneralEOPhaseExtractionQuaternary
  (image dense_or_full_nonproduct_plane nontract_of_nonaffine_plane)
end Q
namespace P
export GeneralEOAffineNetworkOriginalSource (source sourceValue)
end P
namespace S
export GeneralEOPhaseExtractionSource (Pinning inclusion)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {s n : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

def ControlledCountingHard : Prop :=
  ∀ (α : Type) (ea : Encoding α Bool) (f : α→ℕ), SharpPWitness ea f →
    Nonempty (LengthControlledOracleReduction ea encodingNatBool
      (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding f (O.originalValue G))

theorem controlled_hard (M : Network AlgebraicComplex 4) (ML : Labelling M.shape s 1 a)
    (hL : LabelledNetwork.Exact G M ML) (hN : ∀e,M.edge e=Signature.disequality)
    (hE : Signature.CentralSupport M.denote) (hT : ¬EOTract {⟨4,M.denote⟩}) :
    ControlledCountingHard G := by
  intro α ea f w
  exact ⟨GeneralEONonARSPinningSource.source G M ML hL hN hE hT w⟩

theorem pinning_or_controlled_hardness
    (B : Network AlgebraicComplex 2) (BL : Labelling B.shape s 1 a)
    (hBL : LabelledNetwork.Exact G B BL) (hBN : ∀e,B.edge e=Signature.disequality)
    (t : ℂ) (ht : t≠0) (hBt : GeneralEOPhaseExtractionNetwork.Signed (B.map S.inclusion) t)
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign (T.map S.inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map S.inclusion).denote) :
    S.Pinning G ∨ ControlledCountingHard G := by
  obtain ⟨M,ML,hML,hMN,hME,hMP,hMS⟩ := F.nonars_quaternary G S.inclusion B BL hBL hBN t ht hBt
    T TL hL hN hE hSign hA
  have hv : (M.map S.inclusion).denote=Q.image M.denote := by
    funext x
    exact Network.denote_map S.inclusion M x
  rw [hv] at hMP hMS
  rcases Q.dense_or_full_nonproduct_plane M.denote hME hMS hMP with hd|hp
  · right
    exact controlled_hard G M ML hML hMN hME
      (GeneralEONonARSPinningCaps.dense_not_tract M.denote hME hd)
  · obtain ⟨e,hplane,hfull,hnp⟩ := hp
    by_cases haf : Affine (EOBinaryPlaneCore.compress (Tensor.reindex e M.denote))
    · left
      exact ⟨P.source G M ML hML hMN e hplane hfull haf hnp⟩
    · right
      exact controlled_hard G M ML hML hMN hME
        (Q.nontract_of_nonaffine_plane M.denote e _ hplane haf hnp)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionControlledSource
