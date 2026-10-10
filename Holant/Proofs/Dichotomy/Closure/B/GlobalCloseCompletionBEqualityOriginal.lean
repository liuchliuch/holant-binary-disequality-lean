import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityCSP
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNativeCodec
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBQuaternary
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! Whole-original-family classification and source endpoint after a real
B-normalized Eq4 graph. The accumulated basis is the explicit product B·V;
its native edge has the exact multiplier −2i. Thus a successful ordinary test
classifies and evaluates all original current rows, not just the selected q4. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityOriginal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
namespace C
export GlobalCloseCompletionBNativeCodec (mapped source)
end C
namespace S
export GlobalCloseCompletionBEqualityCSP
  (family ordinarySource evenCSPSource squareCSPSource current_included family_eq4 family_pin family_x rejected_iff)
end S
namespace Q
export GlobalCloseCompletionBQuaternary (identity_member old_mapped)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (d : GlobalCloseCompletionBPrimeEq4.Output (C.mapped G P))
local instance : NumberField (OI.K (C.mapped G P)) := OI.numberField (C.mapped G P)

def identityLabel := (Q.identity_member G P).choose

theorem identity_literal :
    (⟨GlobalCloseCompletionBNativeSource.arity G P (identityLabel G P).val,
      C.mapped G P (identityLabel G P)⟩ : AnySignature AlgebraicComplex)=
      ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := (Q.identity_member G P).choose_spec

def ordinarySource := Programme.compose
  (S.ordinarySource (C.mapped G P) d (identityLabel G P) (identity_literal G P)) (C.source G P)
def evenCSPSource := Programme.compose
  (S.evenCSPSource (C.mapped G P) d (identityLabel G P) (identity_literal G P)) (C.source G P)
def squareCSPSource := Programme.compose
  (S.squareCSPSource (C.mapped G P) d (identityLabel G P) (identity_literal G P)) (C.source G P)

abbrev family := S.family (C.mapped G P) d
abbrev current := CurrentFrontierClosure.currentFamily G P
abbrev CurrentTract := TractX (familyAction sourceKBasis (current G P))

theorem normalized_current_included : familyAction basisB.symm (current G P)⊆family G P d := by
  rintro _ ⟨_,⟨_,⟨i,rfl⟩,rfl⟩,rfl⟩
  apply S.current_included (C.mapped G P) d
  exact ⟨GlobalCloseCompletionBOrdinarySource.oldLabel G P i,Q.old_mapped G P i⟩

theorem normalized_preprocessed : Preprocessed (familyAction basisB.symm (current G P)) :=
  Conformal.preprocessed_familyAction basisB.symm (GlobalCloseCompletionEq4Classification.current_preprocessed G P)

theorem normalized_preprocess_included :
    familyAction basisB.symm (current G P)⊆preprocess (family G P d) := by
  intro f hf
  exact ⟨normalized_current_included G P d hf,normalized_preprocessed G P f hf⟩

private theorem target_scale (target : TargetClass) : Conformal.ScaleClosed target.family := by
  cases target
  · exact Conformal.affineClass_scaleClosed
  · exact Conformal.productClass_scaleClosed
  · exact Conformal.localAffineClass_scaleClosed

/-- The actual original-X edge is transported with the same accumulated
matrix used on every current row, and its nonzero B multiplier is retained. -/
theorem common (target : TargetClass)
    (h : CommonTransformable target.family (preprocess (family G P d))) :
    CommonKPresentationInKCoordinates target.family (current G P) := by
  obtain ⟨_,B,basis⟩ := h
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,basisB.comp B,?_,?_⟩
  · change (⟨2,kernelSignature (Kernel.pullback Signature.disequality
      (Kernel.mul basisB.matrix B.matrix))⟩ : AnySignature AlgebraicComplex)∈target.family
    have edge : Kernel.pullback Signature.disequality basisB.matrix=
      scale (-2*imaginaryUnit) Signature.equality := Holant.Marked.edgeB
    rw [pullback_mul,edge]
    change (⟨2,kernelSignature (Kernel.pullback
      (fun b c => (-2*imaginaryUnit)*Signature.equality b c) B.matrix)⟩ :
        AnySignature AlgebraicComplex)∈target.family
    rw [Conformal.pullback_scale]
    exact target_scale target 2 _ basis.1 (-2*imaginaryUnit)
  · intro f hf
    have member : (⟨f.1,basisB.symm.action f.2⟩ : AnySignature AlgebraicComplex)∈
        preprocess (family G P d) := normalized_preprocess_included G P d ⟨f,hf,rfl⟩
    simpa only [InvertibleKernel.comp_symm,InvertibleKernel.comp_action] using basis.2 _ member

theorem tractX_of_tract (tract : Tract (family G P d)) : CurrentTract G P := by
  rcases (StableHigherCurrentAnchorCriterion.tract_iff_one_common_basis
    (S.family_eq4 (C.mapped G P) d)).mp tract with affine | product | localAffine
  · exact ClosureNativePresentation.tractX_forward_affine (common G P d .affine affine)
  · exact ClosureNativePresentation.tractX_forward_product (common G P d .product product)
  · exact ClosureNativePresentation.tractX_forward_localAffine (common G P d .localAffine localAffine)

def originalComputes (tract : Tract (family G P d)) :=
  StablePaletteTractability.originalComputes G P (tractX_of_tract G P d tract)

theorem classified : CurrentTract G P ∨
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (family G P d)) := by
  classical
  by_cases tract : Tract (family G P d)
  · exact Or.inl (tractX_of_tract G P d tract)
  · exact Or.inr ((S.rejected_iff (C.mapped G P) d).mp tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityOriginal
end
