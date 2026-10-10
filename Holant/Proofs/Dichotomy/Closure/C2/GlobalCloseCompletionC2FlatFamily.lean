import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedFlatLeaf
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatDescent
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopOrdinarySource

/-! Whole-current Flat certification supplies the unchanged original-G
polynomial evaluator through one common actual Affine presentation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatFamily
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionStopOrdinarySource (family table_value ordinary native originalComputes)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false

theorem tract_of_affine (F : SignatureFamily AlgebraicComplex) (finite : F.Finite)
    (all : ∀f∈F,Affine f.2) : Tract F := by
  have small : (preprocess F).Finite := finite.subset (fun _ h=>h.1)
  apply TractX.tract
  refine ⟨small,Or.inr (Or.inl ⟨small,InvertibleKernel.identity,?_,?_⟩)⟩
  · have h := SymmetricBinaryPullback.affine_diagonal_of_fourth_power_eq 1 1 one_ne_zero rfl
    change Affine (kernelSignature (Kernel.pullback Signature.equality InvertibleKernel.identity.matrix))
    convert h using 1
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [kernelSignature,Kernel.pullback,Kernel.mul_apply,Kernel.transpose,InvertibleKernel.identity,
        Signature.equality,SymmetricBinaryPullback.diagonal,h0,h1]
  · intro f hf
    change Affine (InvertibleKernel.identity.symm.action f.2)
    simpa only [InvertibleKernel.identity_symm,InvertibleKernel.identity_action] using all f hf.1

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (flat : ∀f∈P.family,GlobalCloseCompletionRetainedFlatLeaf.Predicate G f)

include flat in
theorem tract : Tract (S.family G P) := by
  apply tract_of_affine _ (Set.finite_range _)
  rintro f ⟨i,rfl⟩
  have row := GlobalCloseCompletionC2FlatDescent.affine_of_flatOrZero
    (S.native G P i) (flat ⟨P.arity i.val,P.table i⟩ ⟨i,rfl⟩)
  have transformed := GlobalCloseCompletionC2KAffine.sourceK_affine _ row
  change Affine (RingHomRealization.mapSignature (GlobalCloseCompletionStopOrdinarySource.field G P).subtype
    (GlobalCloseCompletionStopOrdinarySource.table G P i))
  have equation : RingHomRealization.mapSignature (GlobalCloseCompletionStopOrdinarySource.field G P).subtype
      (GlobalCloseCompletionStopOrdinarySource.table G P i)=sourceKBasis.action (S.native G P i) :=
    funext (S.table_value G P i)
  rw [equation]
  exact transformed

def originalComputes := S.originalComputes G P (tract G P flat)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatFamily
end
