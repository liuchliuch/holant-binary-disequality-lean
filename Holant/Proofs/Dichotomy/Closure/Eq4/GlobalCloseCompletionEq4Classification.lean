import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4CommonBasis
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability
import Holant.Proofs.Closure.ClosureNativePresentation
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXLocalExclusion

/-! Whole-current-family classification in the positive ordinary Eq4 branch.
The actual X vertex reconstructs the mandatory native-X edge in the SAME
basis; every retained original row survives preprocessing and the inclusion.
Failure is an explicit finite shared-basis obstruction, not assumed hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Classification
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace S
export GlobalCloseCompletionEq4FullSource
  (family family_x family_eq4 current_included tract_iff_test rejected_iff squareCSPSource)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : GlobalCloseCompletionEq4Graph.Output G P)

abbrev current := CurrentFrontierClosure.currentFamily G P
abbrev CurrentTract := TractX (familyAction sourceKBasis (current G P))

theorem current_preprocessed : Preprocessed (current G P) := by
  rintro _ ⟨f,⟨i,rfl⟩,rfl⟩
  refine ⟨P.positive i,?_⟩
  intro h
  apply P.nonzero i
  funext x
  apply (StableHigherCurrentPurePinsCore.embedding G).injective
  exact (congrFun h x).trans (map_zero _).symm

theorem current_preprocess_included : current G P ⊆ preprocess (S.family G P d) := by
  intro f hf
  exact ⟨S.current_included G P d hf,current_preprocessed G P f hf⟩

theorem x_preprocessed :
    (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
      preprocess (S.family G P d) := by
  refine ⟨S.family_x G P d,by decide,?_⟩
  intro h
  have hh := congrFun h ![false,true]
  simp [kernelSignature,Signature.disequality] at hh

/-- Literal whole-original-current A/P/L membership in one returned basis,
including native edge compatibility, follows from the actual ordinary test. -/
theorem common (target : TargetClass)
    (h : CommonTransformable target.family (preprocess (S.family G P d))) :
    CommonKPresentationInKCoordinates target.family (current G P) := by
  obtain ⟨_,B,basis⟩ := h
  have native := GlobalCloseCompletionEq4CommonBasis.target_native_of_ordinary target
    (preprocess (S.family G P d)) B (x_preprocessed G P d) basis
  exact ⟨CurrentFrontierClosure.currentFamily_finite G P,B,native.1,
    fun f hf => native.2 f (current_preprocess_included G P d hf)⟩

theorem common_of_tract (tract : Tract (S.family G P d)) :
    CommonKPresentationInKCoordinates affineClass (current G P) ∨
    CommonKPresentationInKCoordinates productClass (current G P) ∨
    CommonKPresentationInKCoordinates localAffineClass (current G P) := by
  rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis (S.family_eq4 G P d)).mp tract with
    affine | product | localAffine
  · exact Or.inl (common G P d .affine affine)
  · exact Or.inr (Or.inl (common G P d .product product))
  · exact Or.inr (Or.inr (common G P d .localAffine localAffine))

/-- Literal X and both pins eliminate LocalAffine in this exact source.
The same source's positive branch therefore has a common Affine or Product
basis on the entire original current family. -/
theorem affine_or_product_of_tract (tract : Tract (S.family G P d)) :
    CommonKPresentationInKCoordinates affineClass (current G P) ∨
    CommonKPresentationInKCoordinates productClass (current G P) := by
  have finite : (preprocess (S.family G P d)).Finite :=
    (Set.finite_range _).subset (fun _ h => h.1)
  rcases (OrdinaryNegativeXLocalExclusion.original_tract_iff G P d).mp tract with affine | product
  · rcases affine with ⟨N,_member,hN,basis⟩
    exact Or.inl (common G P d .affine ⟨finite,_,basis⟩)
  · exact Or.inr (common G P d .product
      (commonTransformable_identity finite (product_equality (0 : Fin 2) 1) product))

theorem tractX_of_tract (tract : Tract (S.family G P d)) : CurrentTract G P := by
  rcases affine_or_product_of_tract G P d tract with affine | product
  · exact ClosureNativePresentation.tractX_forward_affine affine
  · exact ClosureNativePresentation.tractX_forward_product product

def originalComputes (tract : Tract (S.family G P d)) :=
  StablePaletteTractability.originalComputes G P (tractX_of_tract G P d tract)

/-- The new source either classifies and evaluates the whole native current
family, or retains the exact finite obstructions needed by a negative source. -/
theorem classified : CurrentTract G P ∨
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (S.family G P d)) := by
  classical
  by_cases tract : Tract (S.family G P d)
  · exact Or.inl (tractX_of_tract G P d tract)
  · exact Or.inr ((S.rejected_iff G P d).mp tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Classification
end
