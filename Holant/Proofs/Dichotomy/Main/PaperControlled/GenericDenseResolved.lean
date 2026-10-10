import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericDenseLiteralX
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCommonBasis

/-! A finite native alphabet with an actual canonical dense source has a
single compatible native basis, or supplies genuine original-G hardness.
The input programme is a concrete native source, never a hardness backend. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.GenericDenseResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace D
export GlobalCloseCompletionGenericDenseLiteralX (Input H data current_included)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (source : D.Input G)
abbrev family := UniversalPairReduction.FiniteFamily.family (D.H G source)
abbrev Hard := PaperControlledHardness.Original G

include source in
theorem classified (preprocessed : Preprocessed (family G source)) :
    (CommonKPresentationInKCoordinates affineClass (family G source) ∨
      CommonKPresentationInKCoordinates productClass (family G source) ∨
      CommonKPresentationInKCoordinates localAffineClass (family G source)) ∨ Hard G := by
  rcases PaperControlledOrdinary.literalX_classified G (D.data G source) with tract|hard
  · exact Or.inl (StableHigherCurrentAnchorCommonBasis.native_common_of_ordinary_tract
      source.canonical.anchor preprocessed (D.current_included G source)
      (GenericLiteralXSource.family_eq4 G (D.data G source)) tract)
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.GenericDenseResolved
end
