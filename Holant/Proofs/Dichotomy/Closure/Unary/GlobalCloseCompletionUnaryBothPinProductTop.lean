import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopTransport

/-! A true cap of the product-plus-top form keeps both tensor summands
whenever the selected unary weight is nonzero. The exact remaining port
weights and scale give a genuine smaller prime. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinProductTop
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace T
export GlobalCloseCompletionUnaryProductTopPrime (value prime)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def oneCap (f : Signature K (n+1)) (i : Fin (n+1)) : Signature K n :=
  fun x=>f (fun j=>(Fin.cons true x : Fin (n+1)→Bool) (Equiv.swap 0 i j))

theorem front_value (w : Fin (n+1)→K) (c d : K) :
    (fun x : Fin n→Bool=>T.value w c d (Fin.cons true x))=
      T.value (fun j=>w j.succ) (c*w 0) d := by
  classical
  funext x
  simp only [T.value,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,ite_true,
    funext_iff,Fin.forall_fin_succ,Bool.true_eq,true_and]
  ring

theorem one_cap_value (w : Fin (n+1)→K) (c d : K) (i : Fin (n+1)) :
    oneCap (T.value w c d) i=
      T.value (fun j=>w (Equiv.swap 0 i j.succ)) (c*w i) d := by
  change (fun x : Fin n→Bool=>Tensor.reindex (Equiv.swap 0 i) (T.value w c d) (Fin.cons true x))=_
  rw [GlobalCloseCompletionUnaryProductTopTransport.reindex,front_value]
  simp only [Equiv.symm_swap,Equiv.swap_apply_left]

theorem one_cap_prime (w : Fin (n+1)→K) (c d : K) (i : Fin (n+1))
    (positive : 0<n) (hc : c≠0) (hd : d≠0) (weight : w i≠0) :
    Prime (⟨n,oneCap (T.value w c d) i⟩ : AnySignature K) := by
  rw [one_cap_value]
  exact T.prime _ _ _ positive (mul_ne_zero hc weight) hd


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinProductTop
end
