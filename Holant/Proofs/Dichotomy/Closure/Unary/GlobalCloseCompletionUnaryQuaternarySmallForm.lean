import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroCapTrees
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryProductTop
import Holant.Proofs.Closure.ClosureSmallArity

/-! Four actual small zero-cap trees determine the quaternary normal form.
A selected nonzero 0,1 interaction forces all cross-block minors to vanish;
the actual ternary cap trees supply the four cubic identities. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternarySmallForm
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Z
export GlobalCloseCompletionUnaryZeroCapTrees (tree graph value liftedTree lifted_small)
end Z
namespace Q
export GlobalCloseCompletionUnaryQuaternaryProductTop (product correction cap reconstruct)
end Q
namespace C
export GlobalCloseCompletionUnaryTernarySmallCubic (cubic of_tree scale)
end C
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double_comm)
export GlobalCloseCompletionUnaryInteractionMatching (caps_no_fork)
export GlobalCloseCompletionUnaryPinnedProduct (cap)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 850000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}

theorem minor_comm (f : Signature K 4) (i j : Fin 4) : I.minor f i j=I.minor f j i := by
  unfold I.minor
  rw [I.double_comm]
  ring

theorem cross (f : Signature K 4)
    (caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i f))
    (edge : I.minor f 0 1≠0) :
    I.minor f 0 2=0 ∧ I.minor f 0 3=0 ∧ I.minor f 1 2=0 ∧ I.minor f 1 3=0 := by
  have reverse : I.minor f 1 0≠0 := by rwa [minor_comm]
  refine ⟨?_,?_,?_,?_⟩
  · by_contra other
    exact I.caps_no_fork f (by decide) caps 0 1 2 (by decide) (by decide) (by decide) edge other
  · by_contra other
    exact I.caps_no_fork f (by decide) caps 0 1 3 (by decide) (by decide) (by decide) edge other
  · by_contra other
    exact I.caps_no_fork f (by decide) caps 1 0 2 (by decide) (by decide) (by decide) reverse other
  · by_contra other
    exact I.caps_no_fork f (by decide) caps 1 0 3 (by decide) (by decide) (by decide) reverse other

variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H 4)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (origin : N.network.denote (fun _=>false)≠0)
variable (small : ∀i,∀g∈(Z.tree H U N scalar scalarNonzero pin0 pin1 origin i).leaves,g.1≤2)

include small in
theorem cap_cubic (i : Fin 4) : C.cubic (Q.cap N.network.denote i)=0 := by
  have h:=C.of_tree (Z.graph H U N i).denote
    (Z.tree H U N scalar scalarNonzero pin0 pin1 origin i) (small i)
  have form : (Z.graph H U N i).denote=(fun x=>scalar*Q.cap N.network.denote i x) := by
    funext x
    exact Z.value H U N scalar pin0 pin1 i x
  rw [form,C.scale] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 scalarNonzero)

include small in
theorem form (edge : I.minor N.network.denote 0 1≠0) :
    N.network.denote=fun x=>Q.product N.network.denote x+
      if x=(fun _=>true) then Q.correction N.network.denote else 0 := by
  have caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i N.network.denote) := by
    intro i
    exact Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArity.tensorClosure_of_saved_tree
      (Z.liftedTree H U N scalar scalarNonzero pin0 pin1 origin (by decide) i)
      (fun n (_ : Signature K n)=>n≤2)
      (Z.lifted_small H U N scalar scalarNonzero pin0 pin1 origin (by decide) small i)
  obtain ⟨h02,h03,h12,h13⟩:=cross N.network.denote caps edge
  have q0 : N.network.denote ![false,false,false,false]≠0 := by
    simpa only [show (![false,false,false,false] : Fin 4→Bool)=(fun _=>false) by
      funext j;fin_cases j <;>rfl] using origin
  exact Q.reconstruct N.network.denote q0 h02 h03 h12 h13
    (cap_cubic H U N scalar scalarNonzero pin0 pin1 origin small)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternarySmallForm
end
