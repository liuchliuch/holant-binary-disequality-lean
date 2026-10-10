import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityCSP
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversal
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! An actual scalar-Eq4 graph over the original current alphabet is consumed
without changing its source field or oracle. This adapter serves Klein q4
outputs and uses the existing real two-pin/X programme and generic terminal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEq4Source
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open FrontierCommonPresentation
namespace E
export GlobalCloseCompletionBEqualityCSP (field presentation arity table eq4Label pinLabel xLabel
  eq4_literal pin_literal x_literal ordinarySource current_included)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
abbrev CurrentTract := GlobalCloseCompletionEq4Classification.CurrentTract G P
abbrev Hard := OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G

def identityLabel : Fin P.count := P.equality.choose

theorem identity_literal : (⟨P.arity (identityLabel G P).val,mapped G P (identityLabel G P)⟩ :
    AnySignature AlgebraicComplex)=⟨2,fun x=>Signature.equality (x 0) (x 1)⟩ := by
  have h := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G)) P.equality.choose_spec
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  change ClosureSourceRows.embedding G (Signature.equality (x 0) (x 1))=Signature.equality (x 0) (x 1)
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [Signature.equality,h0,h1]

variable (d : GlobalCloseCompletionBPrimeEq4.Output (mapped G P))

def data : GenericLiteralXSource.Data G where
  K := E.field (mapped G P) d
  degree := _
  F := E.presentation (mapped G P) d
  size := _
  b := E.arity (mapped G P) d
  H := E.table (mapped G P) d
  e := E.eq4Label (mapped G P)
  p := E.pinLabel (mapped G P)
  x := E.xLabel (mapped G P)
  he := E.eq4_literal (mapped G P) d
  hp := E.pin_literal (mapped G P) d
  hx := E.x_literal (mapped G P) d
  toOriginal := Programme.compose
    (E.ordinarySource (mapped G P) d (identityLabel G P) (identity_literal G P))
    (Programme.compose (OriginalLCodec.fromCoefficient (StableHigherCurrentPurePinsCore.embedding G) P.table)
      P.toOriginal.controlled)

theorem current_included : CurrentFrontierClosure.currentFamily G P⊆GenericLiteralXSource.family G (data G P d) := by
  rintro f ⟨g,⟨i,rfl⟩,rfl⟩
  exact E.current_included (mapped G P) d ⟨i,rfl⟩

theorem common (target : TargetClass)
    (h : CommonTransformable target.family (preprocess (GenericLiteralXSource.family G (data G P d)))) :
    CommonKPresentationInKCoordinates target.family (CurrentFrontierClosure.currentFamily G P) := by
  obtain ⟨_,V,basis⟩ := h
  have x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
      preprocess (GenericLiteralXSource.family G (data G P d)) := by
    refine ⟨GenericLiteralXSource.family_x G (data G P d),by decide,?_⟩
    intro zero
    have hz := congrFun zero ![false,true]
    simp [kernelSignature,Signature.disequality] at hz
  have native := GlobalCloseCompletionEq4CommonBasis.target_native_of_ordinary target _ V x basis
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,V,native.1,?_⟩
  intro f hf
  exact native.2 f ⟨current_included G P d hf,GlobalCloseCompletionEq4Classification.current_preprocessed G P f hf⟩

theorem tractX_of_tract (tract : Tract (GenericLiteralXSource.family G (data G P d))) : CurrentTract G P := by
  rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis
    (GenericLiteralXSource.family_eq4 G (data G P d))).mp tract with affine|product|localAffine
  · exact ClosureNativePresentation.tractX_forward_affine (common G P d .affine affine)
  · exact ClosureNativePresentation.tractX_forward_product (common G P d .product product)
  · exact ClosureNativePresentation.tractX_forward_localAffine (common G P d .localAffine localAffine)

include d in
theorem classified : CurrentTract G P ∨ Hard G := by
  rcases OrdinaryNegativeGenericXUniversal.tract_or_hard G (data G P d) with tract|hard
  · exact Or.inl (tractX_of_tract G P d tract)
  · exact Or.inr hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEq4Source
end
