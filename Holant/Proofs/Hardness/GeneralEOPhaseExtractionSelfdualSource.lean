import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSelfdualQuaternary
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionSource
import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryPinning

/-! Exact source-level residual for an actual selfdual quaternary network.
Dense and nonaffine nonproduct planes yield original-family hardness; affine
nonproduct and tied two-support planes yield literal pin elimination. Only
zero and the two full tensor-product patterns remain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSelfdualSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open FixedGadgetSubstitution UniversalPairReduction
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
namespace L
export GeneralEONonARSPinningFieldBridge (lift labels exact native denote_lift)
end L
namespace Q
export GeneralEOPhaseExtractionSelfdualQuaternary
  (dense_or_plane_residual tiedOrder tied_deq product)
end Q
namespace S
export GeneralEOPhaseExtractionSource (Pinning CountingHard)
end S
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels reboundary_denote)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance originalAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (N : Network AlgebraicComplex 4) (NL : Labelling N.shape s 1 a)
variable (hN : LabelledNetwork.Exact G N NL) (hn : ∀e,N.edge e=Signature.disequality)

/-- The residual records the exact coefficient identity of an actual graph,
including its coordinate permutation and nonzero scalar. -/
def ProductResidual (M : Signature AlgebraicComplex 4) : Prop :=
  ∃e : Equiv.Perm (Fin 4),
    Tensor.reindex e M=EOBinaryPlaneCore.lift (EOBinaryPlaneCore.compress (Tensor.reindex e M)) ∧
      (EOBinaryPlaneCore.compress (Tensor.reindex e M)=0 ∨
        ∃c,c≠0 ∧ ∃b,EOBinaryPlaneCore.compress (Tensor.reindex e M)=Q.product c b)

include hN hn in
/-- Full selfdual q4 source alternative. Tied two-support blocks are consumed
by actual DEQ pin elimination; full affine nonproduct blocks use the accepted
24-copy network source. No generic hardness or pinning backend is assumed. -/
theorem pinning_hardness_or_product
    (hCentral : Signature.CentralSupport N.denote)
    (hSelfdual : SelfDualPinObstruction.SelfDual N.denote) :
    Nonempty (GeneralEOPinEliminationCases.Elimination G) ∨ S.CountingHard G ∨ ProductResidual N.denote := by
  rcases Q.dense_or_plane_residual N.denote hCentral hSelfdual with hd|hp
  · exact Or.inr (Or.inl (GeneralEONonARSPinningSource.witnessCountingHard G N NL hN hn
      hCentral (GeneralEONonARSPinningCaps.dense_not_tract N.denote hCentral hd)))
  obtain ⟨e,hplane,hres⟩ := hp
  rcases hres with hz|ht|hp|hfull
  · exact Or.inr (Or.inr ⟨e,hplane,Or.inl hz⟩)
  · obtain ⟨d,hd,b,hf⟩ := ht
    let QN := R.reboundary (R.reboundary N e) (Q.tiedOrder b)
    let QL := R.reboundaryLabels (R.reboundary N e) (R.reboundaryLabels N NL e) (Q.tiedOrder b)
    have hQ : QN.denote=d • ExactTwoSignatures.E := by
      rw [R.reboundary_denote,R.reboundary_denote,hplane,hf]
      exact Q.tied_deq d b
    exact Or.inl ⟨GeneralOddHigherResidueQuaternaryPinning.deqElimination G QN QL hN hn d hd hQ⟩
  · exact Or.inr (Or.inr ⟨e,hplane,Or.inr hp⟩)
  · by_cases hA : Affine (EOBinaryPlaneCore.compress (Tensor.reindex e N.denote))
    · left
      have r := GeneralEOAffineNetworkOriginalSource.source G N NL hN hn e hplane
        hfull.1 hA hfull.2
      rw [GeneralEOAffineNetworkOriginalSource.literal_source_value] at r
      refine ⟨?_⟩
      apply GeneralEOCentralHoleHardnessPinning.samePalette G (GeneralEOPinnedDescentPalette.pinned G)
        rfl (fun _ => rfl)
      rw [GeneralEOSinglePinPaletteBridge.literal_family]
      exact r
    · exact Or.inr (Or.inl (GeneralEONonARSPinningSource.witnessCountingHard G N NL hN hn
        hCentral (GeneralEOPhaseExtractionQuaternary.nontract_of_nonaffine_plane N.denote e _
          hplane hA hfull.2)))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSelfdualSource
