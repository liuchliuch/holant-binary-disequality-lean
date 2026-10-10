import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardMatchingAffine
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEq4Source

/-! Whole-current native Affine membership supplies the literal identity
common basis, including the native disequality edge. The existing forward-K
bridge then gives the exact CurrentTract endpoint. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCurrentTract
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem native_edge_affine : Affine (kernelSignature (Signature.disequality (K:=AlgebraicComplex))) := by
  convert GlobalCloseCompletionKleinStandardMatchingAffine.E_affine 1 using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [kernelSignature,Signature.disequality,
      Holant.Certificates.EqualityQuaternary.Klein.E,
      Holant.Certificates.EqualityQuaternary.Klein.basisQ,
      Holant.Certificates.EqualityQuaternary.Klein.matrix,
      Holant.Certificates.EqualityQuaternary.Klein.embed_apply,
      QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,h0,h1]

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

theorem common (all : ∀i : Fin P.count,
    Affine (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (P.table i))) :
    CommonKPresentationInKCoordinates affineClass (CurrentFrontierClosure.currentFamily G P) := by
  refine ⟨CurrentFrontierClosure.currentFamily_finite G P,InvertibleKernel.identity,?_,?_⟩
  · simpa [affineClass,InvertibleKernel.identity,Kernel.pullback] using native_edge_affine
  · rintro _ ⟨f,⟨i,rfl⟩,rfl⟩
    simp only [InvertibleKernel.identity_symm,InvertibleKernel.identity_action]
    change Affine (fun x=>Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G (P.table i x))
    have h := all i
    change Affine (fun x=>Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G (P.table i x)) at h
    exact h

theorem current_tract (all : ∀i : Fin P.count,
    Affine (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (P.table i))) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P :=
  ClosureNativePresentation.tractX_forward_affine (common G P all)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineCurrentTract
end
