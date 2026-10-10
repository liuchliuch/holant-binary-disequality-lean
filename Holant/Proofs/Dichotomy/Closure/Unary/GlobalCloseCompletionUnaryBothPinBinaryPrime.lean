import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinColumnProjection
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryHigh

/-! The normalized high-arity binary branch under both pin projections.
The original anchored minor selects the binary factor internally; primality
forbids its top column, and the actual ordinary outside loop is nonsmall. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinBinaryPrime
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace C
export GlobalCloseCompletionUnaryBinaryCaps (factor factor_origin factor_det columns first second)
end C
namespace G
export GlobalCloseCompletionUnaryBinaryLoopGraph (sumPorts)
end G
namespace R
export GlobalCloseCompletionUnaryPinLoopFactor (block zeroPair zeroPair_ne_one proper_split)
end R
namespace L
export GlobalCloseCompletionUnaryBinaryLoop (join loop)
end L
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
export GlobalCloseCompletionUnaryPinnedProduct (cap)
end I
namespace B
export GlobalCloseCompletionUnaryBinaryFactor (pair)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {t : ℕ}

theorem word_sumPorts (x : Fin 2→Bool) (y : Fin (t+2)→Bool) :
    (fun i=>Sum.elim x y ((G.sumPorts t).symm i))=L.join x y := by
  funext i
  refine Fin.cases rfl (fun j=>Fin.cases rfl (fun _=>rfl) j) i

theorem block_sumPorts (f : Signature K (t+4)) :
    R.block (G.sumPorts t) f=(fun x y=>f (L.join x y)) := by
  funext x y
  exact congrArg f (word_sumPorts x y)

theorem first_sumPorts : C.first (G.sumPorts t)=(0 : Fin (t+4)) := rfl
theorem second_sumPorts : C.second (G.sumPorts t)=(1 : Fin (t+4)) := rfl

theorem top_forbidden (f : Signature K (t+4))
    (prime : Prime (⟨t+4,f⟩ : AnySignature K)) (g : Signature K 2)
    (columns : ∀y,y≠(fun _=>true)→∃c : K,∀x,R.block (G.sumPorts t) f x y=g x*c) :
    ¬∃c : K,∀x,R.block (G.sumPorts t) f x (fun _=>true)=g x*c := by
  rintro ⟨ct,top⟩
  obtain ⟨cb,bottom⟩ := columns R.zeroPair R.zeroPair_ne_one
  obtain ⟨h,split⟩ := R.proper_split (G.sumPorts t) f g (by decide) columns
    ⟨cb+ct,by intro x;rw [bottom,top,mul_add]⟩
  exact prime.2 ⟨⟨2,g⟩,⟨t+2,h⟩,split⟩

theorem loop_not_small (positive : 0<t) (f : Signature K (t+4))
    (prime : Prime (⟨t+4,f⟩ : AnySignature K)) (origin : f (fun _=>false)≠0)
    (edge : I.minor f 0 1≠0)
    (caps : ∀i : Fin (t+4),∀b : Bool,
      Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (fun z=>f (Function.update z i b))) :
    ¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2)
      (L.loop (R.block (G.sumPorts t) f)) := by
  let g := C.factor (G.sumPorts t) f
  have g0 : g (fun _=>false)≠0 := by
    rw [show g=C.factor (G.sumPorts t) f from rfl,C.factor_origin _ f origin]
    exact one_ne_zero
  have det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0 := by
    rw [show g=C.factor (G.sumPorts t) f from rfl,C.factor_det _ f origin,first_sumPorts,second_sumPorts]
    exact div_ne_zero edge (pow_ne_zero 2 origin)
  have zeroCaps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i f) :=
    fun i=>caps i false
  have columns := C.columns (G.sumPorts t) f origin (by simpa only [first_sumPorts,second_sumPorts] using edge) zeroCaps
  have top := top_forbidden f prime g columns
  rw [block_sumPorts] at columns top ⊢
  refine GlobalCloseCompletionUnaryBothPinColumnProjection.cap_loop_not_small positive f g g0 det
    (f (fun _=>false)) origin ?_ columns top ?_
  · intro x
    change f (L.join x (fun _=>false))=
      (f (B.pair (C.first (G.sumPorts t)) (C.second (G.sumPorts t)) (x 0) (x 1))/f (fun _=>false))*f (fun _=>false)
    rw [first_sumPorts,second_sumPorts,GlobalCloseCompletionUnaryBothPinColumn.pair_join]
    exact (div_mul_cancel₀ _ origin).symm
  · intro k
    exact caps k.succ.succ true


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinBinaryPrime
end
