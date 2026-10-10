import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFactorCaps
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryHighSelector

/-! A nonsmall live-origin graph contains an actual nonbinary prime graph.
Its selected factor is physically isolated by the retained zero pin. The
chosen smaller graph uses exactly the same source table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPrimeSubgraph
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace F
export GlobalCloseCompletionUnaryFactorCaps (exists_leaf)
export GlobalCloseCompletionUnaryHighSelector (leaf_arity_le)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}

def zeroDecomposition (K : Type) [Field K] (n : ℕ) : TensorDecomposition K n where
  count:=n
  arity _:=1
  factor _ _:=0
  ports := {
    toFun := fun p=>p.1
    invFun := fun i=>⟨i,0⟩
    left_inv := by
      rintro ⟨i,j⟩
      have h : j=0 := Fin.eq_zero j
      subst j
      rfl
    right_inv := fun _=>rfl }
  scale:=1

theorem zero_small (positive : 0<n) : Signature.TensorClosure (fun m (_ : Signature K m)=>m≤2) (0 : Signature K n) := by
  refine ⟨zeroDecomposition K n,(fun _=>by change 1≤2;decide),?_⟩
  funext x
  simp [TensorDecomposition.value,zeroDecomposition,positive.ne']

theorem nonzero_of_nonsmall (positive : 0<n) (f : Signature K n)
    (nonsmall : ¬Signature.TensorClosure (fun m (_ : Signature K m)=>m≤2) f) : f≠0 := by
  intro zero
  apply nonsmall
  rw [zero]
  exact zero_small positive

variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H n)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (origin : N.network.denote (fun _=>false)≠0)
include scalarNonzero pin0 pin1 origin in
theorem exists_prime
    (nonsmall : ¬Signature.TensorClosure (fun m (_ : Signature K m)=>m≤2) N.network.denote) :
    ∃m,3≤m ∧ m≤n ∧ ∃V : NoXOrdinaryGraphAdjoin.Output H m,
      Prime (⟨m,V.network.denote⟩ : AnySignature K) ∧ V.network.denote (fun _=>false)≠0 := by
  have nonzero : N.network.denote≠0 := by intro zero;exact origin (congrFun zero (fun _=>false))
  obtain ⟨t⟩:=exists_factorTree (⟨n,N.network.denote⟩ : AnySignature K) nonzero
  have large : ∃g∈t.leaves,3≤g.1 := by
    by_contra none
    push Not at none
    apply nonsmall
    exact Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArity.tensorClosure_of_saved_tree
      t (fun m (_ : Signature K m)=>m≤2) (fun g hg=>by have h:=none g hg;omega)
  obtain ⟨g,member,big⟩:=large
  obtain ⟨V,prime,live,c,hc,form⟩:=F.exists_leaf H U N scalar scalarNonzero pin0 pin1 origin t g member
  exact ⟨g.1,big,F.leaf_arity_le t member,V,prime,live⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPrimeSubgraph
end
