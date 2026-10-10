import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralDenseCanonical
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericDenseResolved
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification
import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeCurrent

/-! A canonical actual O endpoint classifies the entire unchanged current
palette. Its coefficient codec is converted by the existing faithful map and
the actual palette-to-original programme is composed without a new oracle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDenseResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
abbrev family := UniversalPairReduction.FiniteFamily.family (mapped G P)

theorem family_current : family G P=CurrentFrontierClosure.currentFamily G P := by
  ext g
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩

theorem family_ambient : family G P=ClosureSourceRows.ambientFamily G P := by
  ext g
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩

variable (chart : GlobalCloseCompletionBDenseCanonical.Canonical (ClosureSourceRows.ambientFamily G P))

def input : GlobalCloseCompletionGenericDenseLiteralX.Input G where
  count := P.count
  arity := P.arity
  table := mapped G P
  identity := by
    change Holant.LocalDrafts.FinitePGL2.Stabilization.RetainsIdentity (family G P)
    rw [family_ambient]
    exact StableDenseGaugeCurrent.ambient_identity G P
  canonical := by
    change GlobalCloseCompletionBDenseCanonical.Canonical (family G P)
    rw [family_ambient]
    exact chart
  source := Programme.compose
    (OriginalLCodec.fromCoefficient (StableHigherCurrentPurePinsCore.embedding G) P.table)
    P.toOriginal.controlled

include chart in
theorem classified : GlobalCloseCompletionEq4Classification.CurrentTract G P ∨
    OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G := by
  have hp : Preprocessed (family G P) := by
    rw [family_current]
    exact GlobalCloseCompletionEq4Classification.current_preprocessed G P
  rcases GlobalCloseCompletionGenericDenseResolved.classified G (input G P chart) hp with
    (affine|product|localAffine)|hard
  · change CommonKPresentationInKCoordinates affineClass (family G P) at affine
    rw [family_current] at affine
    exact Or.inl (ClosureNativePresentation.tractX_forward_affine affine)
  · change CommonKPresentationInKCoordinates productClass (family G P) at product
    rw [family_current] at product
    exact Or.inl (ClosureNativePresentation.tractX_forward_product product)
  · change CommonKPresentationInKCoordinates localAffineClass (family G P) at localAffine
    rw [family_current] at localAffine
    exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine localAffine)
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDenseResolved
end
