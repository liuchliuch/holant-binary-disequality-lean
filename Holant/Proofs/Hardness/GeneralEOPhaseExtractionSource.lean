import Holant.Proofs.Hardness.GeneralEOPhaseExtractionFieldBridge
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionQuaternary
import Holant.Proofs.Hardness.GeneralEOAffineNetworkOriginalSource
import Holant.Proofs.Hardness.GeneralEONonARSPinningCaps

/-! Conditional finite-phase source: an actual signed cap,
and a non-ARS original-labelled EO graph with a common complement sign,
supply either full literal pin elimination or original-family counting
hardness. Neither branch is a premise, oracle, or assumed backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution
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
namespace H
export GeneralEONonARSPinningSource (witnessCountingHard)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {s n : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

abbrev inclusion : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).subtype

def Pinning : Prop := Nonempty (LengthControlledOracleReduction
  (GeneralEOSinglePinAmplificationProgramme.inputEncoding (s:=s) (a:=a))
  (O.originalPresentation G).encoding (RawClosedNetwork.validatedEncoding s 1 a)
  (O.originalPresentation G).encoding (P.sourceValue G) (O.originalValue G))

def CountingHard : Prop := Holant.LocalDrafts.CountingHardness.WitnessCountingHard
  (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding (O.originalValue G)

theorem pinning_or_hardness
    (B : Network AlgebraicComplex 2) (BL : Labelling B.shape s 1 a)
    (hBL : LabelledNetwork.Exact G B BL) (hBN : ∀e,B.edge e=Signature.disequality)
    (t : ℂ) (ht : t≠0) (hBt : GeneralEOPhaseExtractionNetwork.Signed (B.map inclusion) t)
    (T : Network AlgebraicComplex n) (TL : Labelling T.shape s 1 a)
    (hL : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign (T.map inclusion).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map inclusion).denote) :
    Pinning G ∨ CountingHard G := by
  obtain ⟨M,ML,hML,hMN,hME,hMP,hMS⟩ := F.nonars_quaternary G inclusion B BL hBL hBN t ht hBt
    T TL hL hN hE hSign hA
  have hv : (M.map inclusion).denote=Q.image M.denote := by
    funext x
    exact Network.denote_map inclusion M x
  rw [hv] at hMP hMS
  rcases Q.dense_or_full_nonproduct_plane M.denote hME hMS hMP with hd|hp
  · right
    exact H.witnessCountingHard G M ML hML hMN hME
      (GeneralEONonARSPinningCaps.dense_not_tract M.denote hME hd)
  · obtain ⟨e,hplane,hfull,hnp⟩ := hp
    by_cases haf : Affine (EOBinaryPlaneCore.compress (Tensor.reindex e M.denote))
    · left
      exact ⟨P.source G M ML hML hMN e hplane hfull haf hnp⟩
    · right
      exact H.witnessCountingHard G M ML hML hMN hME
        (Q.nontract_of_nonaffine_plane M.denote e _ hplane haf hnp)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSource
