import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralMixingResources
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddRelabel

/-! Literal inclusion carries all three actual supplier forms into one
common retained palette, preserving exact coefficient and phase hypotheses. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixingRelabel
open Holant Holant.Tractable
open OrdinaryNegativeXUniversalResource NoXGeneralMixingResources
namespace R
export NoXGeneralOddRelabel (resource ambient)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s t : ℕ} {a b : ℕ→ℕ}
variable (F : (i : Fin s)→Signature K (a i.val)) (H : (i : Fin t)→Signature K (b i.val))
variable (labels : Fin s→Fin t)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=⟨a i.val,F i⟩)
variable {kind : Kind}

def alpha (row : AlphaResource F kind) : AlphaResource H kind where
  toOddResource:=R.resource F H labels literal row.toOddResource
  alpha:=by rw [R.ambient];exact row.alpha
  full:=by rw [R.ambient];exact row.full

def affine (row : AffineResource F kind) : AffineResource H kind where
  toOddResource:=R.resource F H labels literal row.toOddResource
  affine:=by rw [R.ambient];exact row.affine
  full:=by rw [R.ambient];exact row.full

def oppositeAlpha (row : OppositeAlpha F kind) : OppositeAlpha H kind where
  toOddResource:=R.resource F H labels literal row.toOddResource
  alpha:=by rw [R.ambient];exact row.alpha
  full:=by rw [R.ambient];exact row.full

def oppositeAffine (row : OppositeAffine F kind) : OppositeAffine H kind where
  toOddResource:=R.resource F H labels literal row.toOddResource
  affine:=by rw [R.ambient];exact row.affine
  full:=by rw [R.ambient];exact row.full

def unary (row : FullUnary F) : FullUnary H where
  toOddResource:=R.resource F H labels literal row.toOddResource
  full:=by rw [R.ambient];exact row.full

include literal in
theorem ordinary (h : OrdinarySupply F) : OrdinarySupply H := by
  rcases h with ⟨kind,⟨row⟩⟩|⟨kind,⟨row⟩⟩
  · exact Or.inl ⟨kind,⟨alpha F H labels literal row⟩⟩
  · exact Or.inr ⟨kind,⟨oppositeAlpha F H labels literal row⟩⟩
include literal in
theorem uniform (h : UniformSupply F) : UniformSupply H := by
  rcases h with ⟨kind,⟨row⟩⟩|⟨kind,⟨row⟩⟩
  · exact Or.inl ⟨kind,⟨affine F H labels literal row⟩⟩
  · exact Or.inr ⟨kind,⟨oppositeAlpha F H labels literal row⟩⟩
include literal in
theorem localSupply (h : LocalSupply F) : LocalSupply H := by
  rcases h with unaryCase|⟨kind,⟨row⟩⟩
  · obtain ⟨row⟩ := unaryCase
    exact Or.inl ⟨unary F H labels literal row⟩
  · exact Or.inr ⟨kind,⟨oppositeAffine F H labels literal row⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralMixingRelabel
end
