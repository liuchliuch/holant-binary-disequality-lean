import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CurrentSource
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CommonBasis

/-! The actual source native-X binary, retained before Hadamard coordinates,
provides the inverse weighted-edge row Z/2 in the finite normalized family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CurrentNativeRow
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionA0CurrentSource (retained count arity mapped family)
end C
namespace W
export GlobalCloseCompletionA0Workfield (basis table table_value)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

theorem member : (⟨2,W.basis.symm.action (kernelSignature Signature.disequality)⟩ :
    AnySignature AlgebraicComplex)∈C.family G P torsion q core literal := by
  obtain ⟨j,hj⟩ := ClosureSourceRows.native_retained G P torsion q core literal (by decide : 2≤2)
  refine ⟨GlobalCloseCompletionA0XSource.oldLabel G (C.retained G P torsion q core literal) j,?_⟩
  have h := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G))
    (GlobalCloseCompletionA0NativeSource.old_signature G (C.retained G P torsion q core literal) j)
  refine h.trans ?_
  have hv : RingHomRealization.mapAny (ClosureSourceRows.embedding G)
      ⟨(C.retained G P torsion q core literal).arity j.val,
        W.table G (C.retained G P torsion q core literal) j⟩=
      (⟨(C.retained G P torsion q core literal).arity j.val,
        W.basis.symm.action (StableHigherCurrentPurePinsCore.mapped G (C.retained G P torsion q core literal) j)⟩ :
          AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex _ => (⟨_,f⟩ : AnySignature AlgebraicComplex))
    exact funext (W.table_value G (C.retained G P torsion q core literal) j)
  refine hv.trans ?_
  have hh := congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,W.basis.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2)⟩ :
      AnySignature AlgebraicComplex)) hj
  refine hh.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,W.basis.symm.action f⟩ : AnySignature AlgebraicComplex))
  funext x
  change ClosureSourceRows.embedding G (Signature.disequality (x 0) (x 1))=
    Signature.disequality (x 0) (x 1)
  cases x 0 <;> cases x 1 <;> simp [Signature.disequality]

theorem nonzero : W.basis.symm.action (kernelSignature Signature.disequality)≠0 := by
  intro h
  have h2 := congrArg (fun f : Signature AlgebraicComplex 2 => f (fun _ => false)) h
  rw [GlobalCloseCompletionA0CommonBasis.native_action] at h2
  norm_num [GlobalCloseCompletionA0CommonBasis.native,GlobalCloseCompletionA0CommonBasis.basis,
    GlobalCloseCompletionA0Workfield.basis,ClosureMarkedDihedralA0.basis,ClosureMarkedCyclic.basis,
    Holant.Marked.basisA,Holant.Marked.UAInv,
    GlobalCloseCompletionEq4CommonBasis.transpose,InvertibleKernel.comp,InvertibleKernel.symm,
    bitFlipBasis,kernelSignature,Kernel.mul_apply,Kernel.transpose,Signature.disequality] at h2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CurrentNativeRow
end
