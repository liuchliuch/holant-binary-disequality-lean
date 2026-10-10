import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.NoIOrdinaryComplete
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.AnchorSource
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryAnchorCommon

/-! Whole-family no-I anchor classification with the exact native oracle
as endpoint and a retained controlled programme for every counted verifier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.AnchorComplete
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export NoIOrdinaryRaw.AnchorSource (build transformed_included nativeTarget nativeIdentity)
end D
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (T : NoIOrdinaryRaw.Target)
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family H))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) (O.originalPresentation H).encoding
  T.inputEncoding T.outputEncoding (O.originalValue H) T.value)

include A back in
theorem classified :
    (CommonKPresentationInKCoordinates affineClass (preprocess (UniversalPairReduction.FiniteFamily.family H)) ∨
      CommonKPresentationInKCoordinates productClass (preprocess (UniversalPairReduction.FiniteFamily.family H)) ∨
      CommonKPresentationInKCoordinates localAffineClass (preprocess (UniversalPairReduction.FiniteFamily.family H))) ∨ T.Hard := by
  let src:=D.build T H A back
  rcases NoIOrdinaryRaw.NoIOrdinaryComplete.classified T src with positive|hard
  · left
    rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis
      (NoIOrdinaryRaw.GenericOrdinarySource.family_eq4 T src)).mp positive with affine|product|localAffine
    · exact Or.inl (NoIOrdinaryAnchorCommon.common Conformal.affineClass_scaleClosed A (Set.finite_range _)
        (D.transformed_included T H A back) affine)
    · exact Or.inr (Or.inl (NoIOrdinaryAnchorCommon.common Conformal.productClass_scaleClosed A (Set.finite_range _)
        (D.transformed_included T H A back) product))
    · exact Or.inr (Or.inr (NoIOrdinaryAnchorCommon.common Conformal.localAffineClass_scaleClosed A (Set.finite_range _)
        (D.transformed_included T H A back) localAffine))
  · exact Or.inr hard

include A in
theorem native_classified :
    (CommonKPresentationInKCoordinates affineClass (preprocess (UniversalPairReduction.FiniteFamily.family H)) ∨
      CommonKPresentationInKCoordinates productClass (preprocess (UniversalPairReduction.FiniteFamily.family H)) ∨
      CommonKPresentationInKCoordinates localAffineClass (preprocess (UniversalPairReduction.FiniteFamily.family H))) ∨
      (D.nativeTarget H).Hard := classified (D.nativeTarget H) H A (D.nativeIdentity H)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.AnchorComplete
end
