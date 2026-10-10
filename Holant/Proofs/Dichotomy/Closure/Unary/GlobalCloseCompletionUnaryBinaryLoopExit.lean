import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryLoop

/-! The binary-factor high-arity UPF step has no stable prime remainder.
After the same factor has propagated across all zero caps, one ordinary
loop either has a non-small tensor factorization or is a genuine nonzero
zero-origin graph. Otherwise exact reconstruction splits the original prime. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryLoopExit
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace R
export GlobalCloseCompletionUnaryPinLoopFactor (block proper_split)
end R
namespace L
export GlobalCloseCompletionUnaryBinaryLoop (loop propagate)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] {m k : ℕ}

theorem exit (ports : (Fin 2 ⊕ Fin (m+2)) ≃ Fin k) (f : Signature K k)
    (prime : Prime (⟨k,f⟩ : AnySignature K)) (positive : 0<m) (g : Signature K 2)
    (origin : g (fun _=>false)≠0)
    (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
    (caps : ∀y,y≠(fun _=>true)→∃c : K,∀x,R.block ports f x y=g x*c) :
    ¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (L.loop (R.block ports f)) ∨
      (L.loop (R.block ports f)≠0 ∧ L.loop (R.block ports f) (fun _=>false)=0) := by
  classical
  by_cases small : Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (L.loop (R.block ports f))
  · right
    have noRegular : ¬(L.loop (R.block ports f)=0 ∨ L.loop (R.block ports f) (fun _=>false)≠0) := by
      intro regular
      have loopFactor:=L.propagate (R.block ports f) g positive origin det caps small regular
      obtain ⟨h,split⟩:=R.proper_split ports f g (by decide) caps loopFactor
      exact prime.2 ⟨⟨2,g⟩,⟨m+2,h⟩,split⟩
    push Not at noRegular
    exact noRegular
  · exact Or.inl small

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryLoopExit
end
