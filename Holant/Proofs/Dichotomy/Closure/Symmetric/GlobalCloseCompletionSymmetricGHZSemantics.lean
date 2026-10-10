import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZRootInverse
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZGram

/-! Exact ambient semantics of the physical GHZ cap, its implemented inverse,
and its normalized square. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZSemantics
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.FinitePGL2.Stabilization
open OrdinaryNegativeCubicGadgets Holant.Complexity.BinaryInterpolation
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (cap cap_value symmetric)
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz)
end C
namespace Fr
export GlobalCloseCompletionSymmetricGHZFrame (weight capKernel cap_ghz cap_weights_nonzero frame)
end Fr
namespace Rt
export GlobalCloseCompletionSymmetricGHZRootInverse (Extension mapped_left mapped_right)
end Rt
namespace Gr
export GlobalCloseCompletionSymmetricGHZGram (scale square_gram)
end Gr
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
section Generic
variable {K : Type} [Field K] {r n : ℕ} {b : ℕ→ℕ}
variable (phi : K→+*AlgebraicComplex) (H : (i : Fin r)→Signature K (b i.val))

def output (N : Macro H n) : NoXOrdinaryGraphAdjoin.Output H n:=
  ⟨N.network,N.labels,N.exact,N.edges⟩

theorem trace_mapped (N : Macro H 2) (A : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote=kernelSignature A) :
    phi (Matrix.trace (binaryMatrix N.network.denote))=Matrix.trace A := by
  simp only [Matrix.trace,map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact congrFun form ![v,v]

theorem det_mapped (N : Macro H 2) (A : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote=kernelSignature A) :
    phi (Matrix.det (binaryMatrix N.network.denote))=SymmetricBinaryPullback.determinant A := by
  simp only [det_entries,map_sub,map_mul,SymmetricBinaryPullback.determinant,binaryMatrix]
  exact congrArg₂ (fun x y : AlgebraicComplex=>x-y)
    (congrArg₂ (fun x y : AlgebraicComplex=>x*y) (congrFun form ![false,false]) (congrFun form ![true,true]))
    (congrArg₂ (fun x y : AlgebraicComplex=>x*y) (congrFun form ![false,true]) (congrFun form ![true,false]))

theorem trace_zero (N : Macro H 2) (A : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote=kernelSignature A)
    (zero : Matrix.trace A=0) : Matrix.trace (binaryMatrix N.network.denote)=0 := by
  apply phi.injective
  rw [trace_mapped phi H N A form,zero,map_zero]

theorem det_nonzero (N : Macro H 2) (A : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote=kernelSignature A)
    (nonzero : SymmetricBinaryPullback.determinant A≠0) : Matrix.det (binaryMatrix N.network.denote)≠0 := by
  intro zero
  apply nonzero
  rw [←det_mapped phi H N A form,zero,map_zero]

theorem cap_mapped (N : Macro H 3) (U : Macro H 1) (M : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote=C.ghz M.matrix) :
    RingHomRealization.mapSignature phi (C.cap N U).network.denote=
      kernelSignature (Fr.capKernel M
        (Fr.weight M (fun v=>phi (U.network.denote (fun _=>v))) false)
        (Fr.weight M (fun v=>phi (U.network.denote (fun _=>v))) true)) := by
  funext x
  change phi ((C.cap N U).network.denote x)=_
  rw [C.cap_value,map_add,map_mul,map_mul]
  rw [show phi (N.network.denote ![false,x 0,x 1])=C.ghz M.matrix ![false,x 0,x 1] from congrFun form _,
    show phi (N.network.denote ![true,x 0,x 1])=C.ghz M.matrix ![true,x 0,x 1] from congrFun form _]
  exact Fr.cap_ghz M (fun v=>phi (U.network.denote (fun _=>v))) x
end Generic

theorem action_scale (R : InvertibleKernel) {n : ℕ} (c : AlgebraicComplex) (f : Signature AlgebraicComplex n) :
    R.action (fun x=>c*f x)=fun x=>c*R.action f x := by
  funext x
  simp only [InvertibleKernel.action,Signature.coordinateAction,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem normalized_square (R : InvertibleKernel) (B J : Kernel AlgebraicComplex) (c : AlgebraicComplex)
    (hc : c≠0) (normalized : Kernel.pullback J R.matrix=Signature.equality)
    (inverse : Kernel.mul B J=Gr.scale c Signature.equality) :
    R.symm.action (kernelSignature (Gr.scale (c^2)⁻¹ (Kernel.mul B B)))=
      kernelSignature (Kernel.pullback Signature.equality R.matrix) := by
  change R.symm.action (fun x=>(c^2)⁻¹*kernelSignature (Kernel.mul B B) x)=_
  rw [action_scale,Gr.square_gram R B J c normalized inverse]
  funext x
  change (c^2)⁻¹*((c^2)*_)=_
  rw [←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ hc),one_mul]
  rfl

variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (N : Macro H 3) (U : Macro H 1) (M : InvertibleKernel)
variable (form : RingHomRealization.mapSignature L.subtype N.network.denote=C.ghz M.matrix)
variable (D : Rt.Extension L F H (output H (C.cap N U)))

theorem inverse_left : Kernel.mul (fun p q=>(D.inverse p q : AlgebraicComplex))
    (fun p q=>(binaryMatrix (L:=L) (C.cap N U).network.denote p q : AlgebraicComplex))=
    Gr.scale (D.scalar : AlgebraicComplex) Signature.equality := by
  have h:=Rt.mapped_left L F H (output H (C.cap N U)) D
  funext p q
  have e:=congrFun₂ h p q
  simpa [Kernel.mul,Matrix.mul_apply,Matrix.map_apply,Matrix.one_apply,Gr.scale,Signature.equality,GlobalCloseCompletionSymmetricGHZInverse.matrix,output] using e

theorem inverse_right : Kernel.mul
    (fun p q=>(binaryMatrix (L:=L) (C.cap N U).network.denote p q : AlgebraicComplex))
    (fun p q=>(D.inverse p q : AlgebraicComplex))=
    Gr.scale (D.scalar : AlgebraicComplex) Signature.equality := by
  have h:=Rt.mapped_right L F H (output H (C.cap N U)) D
  funext p q
  have e:=congrFun₂ h p q
  simpa [Kernel.mul,Matrix.mul_apply,Matrix.map_apply,Matrix.one_apply,Gr.scale,Signature.equality,GlobalCloseCompletionSymmetricGHZInverse.matrix,output] using e

include form in
theorem frame (det : Matrix.det (binaryMatrix (C.cap N U).network.denote)≠0) :
    ∃R : InvertibleKernel,
      Kernel.pullback (fun p q=>(D.inverse p q : AlgebraicComplex)) R.matrix=Signature.equality ∧
      ∃p q : AlgebraicComplex,p≠0 ∧ q≠0 ∧ R.symm.action (C.ghz M.matrix)=C.symmetric p 0 0 q := by
  let u : Bool→AlgebraicComplex:=fun v=>(U.network.denote (fun _=>v) : AlgebraicComplex)
  have cap : RingHomRealization.mapSignature (L.val.toRingHom : L→+*AlgebraicComplex)
      (C.cap N U).network.denote=kernelSignature (Fr.capKernel M (Fr.weight M u false) (Fr.weight M u true)) :=
    cap_mapped (L.val.toRingHom : L→+*AlgebraicComplex) H N U M form
  have equality : (fun p q=>(binaryMatrix (L:=L) (C.cap N U).network.denote p q : AlgebraicComplex))=
      Fr.capKernel M (Fr.weight M u false) (Fr.weight M u true) := by
    funext p q
    exact congrFun cap ![p,q]
  have determinant : SymmetricBinaryPullback.determinant (Fr.capKernel M (Fr.weight M u false) (Fr.weight M u true))≠0 := by
    have value := det_mapped (L.val.toRingHom : L→+*AlgebraicComplex) H (C.cap N U) _ cap
    change (L.val.toRingHom : L→+*AlgebraicComplex) (Matrix.det (binaryMatrix (C.cap N U).network.denote)) = _ at value
    have live := (map_ne_zero (L.val.toRingHom : L→+*AlgebraicComplex)).mpr det
    simpa only [value] using live
  have weights:=Fr.cap_weights_nonzero M _ _ determinant
  have inverse:=inverse_left L F H N U D
  rw [equality] at inverse
  exact Fr.frame M _ _ weights.1 weights.2 _ (D.scalar : AlgebraicComplex)
    ((map_ne_zero (D.K.val.toRingHom : D.K→+*AlgebraicComplex)).mpr D.nonzero) inverse


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZSemantics
end
