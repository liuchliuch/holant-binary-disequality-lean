import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary
import Holant.Proofs.Dichotomy.Closure.Dense.GlobalCloseCompletionDenseLiteralX
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! The actual dense canonical Eq4/X receipt is fully consumed. One common
ordinary test either pulls back through the same anchor matrix to the whole
current family or supplies genuine counting hardness of unchanged original G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.DenseResolved
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (C : GlobalCloseCompletionBDenseCanonical.Canonical (ClosureSourceRows.ambientFamily G P))
abbrev source := GlobalCloseCompletionDenseLiteralX.data G P C
abbrev family := GenericLiteralXSource.family G (source G P C)
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G P
abbrev Hard := PaperControlledHardness.Original G

private theorem ambient_current : ClosureSourceRows.ambientFamily G P=
    CurrentFrontierClosure.currentFamily G P := rfl

theorem tractX_of_tract (tract : Tract (family G P C)) : CurrentTract G P := by
  have preprocessed : Preprocessed (ClosureSourceRows.ambientFamily G P) := by
    rw [ambient_current]
    exact GlobalCloseCompletionEq4Classification.current_preprocessed G P
  rcases StableHigherCurrentAnchorCommonBasis.native_common_of_ordinary_tract C.anchor
    preprocessed (GlobalCloseCompletionDenseLiteralX.current_included G P C)
    (GenericLiteralXSource.family_eq4 G (source G P C)) tract with affine|product|localAffine
  · rw [ambient_current] at affine
    exact ClosureNativePresentation.tractX_forward_affine affine
  · rw [ambient_current] at product
    exact ClosureNativePresentation.tractX_forward_product product
  · rw [ambient_current] at localAffine
    exact ClosureNativePresentation.tractX_forward_localAffine localAffine

include C in
theorem classified : CurrentTract G P ∨ Hard G := by
  rcases PaperControlledOrdinary.literalX_classified G (source G P C) with tract|hard
  · exact Or.inl (tractX_of_tract G P C tract)
  · exact Or.inr hard

def originalComputes (tract : Tract (family G P C)) :=
  StablePaletteTractability.originalComputes G P (tractX_of_tract G P C tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.DenseResolved
end
