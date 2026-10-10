import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternarySmallForm
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryMarginal
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPortOrder
import Holant.Proofs.FiniteGroups.Stabilization.LeafExposure

/-! The complete quaternary selector from an actual prime and actual zero
pin. It chooses the interaction order and all cap trees internally, then
returns an actual ternary prime, nonsingular paired quaternary, or genuine
nonzero zero-origin graph. All outputs retain the original labelled table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternarySelector
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Z
export GlobalCloseCompletionUnaryZeroCapTrees (tree output liftedTree lifted_small)
end Z
namespace Q
export GlobalCloseCompletionUnaryQuaternaryProductTop (product correction reconstruct)
export GlobalCloseCompletionUnaryQuaternaryForm (Paired determinant paired nonsingular)
export GlobalCloseCompletionUnaryQuaternarySmallForm (cross cap_cubic)
end Q
namespace M
export GlobalCloseCompletionUnaryQuaternaryMarginal (output alternative)
end M
namespace O
export GlobalCloseCompletionUnaryPortOrder (ordered ordered_edge prime origin)
end O
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
export GlobalCloseCompletionUnaryPinnedProduct (single cap)
export GlobalCloseCompletionUnaryNoInteractions (NoInteractions)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H 4)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K))
variable (origin : N.network.denote (fun _=>false)≠0)

include prime origin in
theorem exists_order : ∃V : NoXOrdinaryGraphAdjoin.Output H 4,
    Prime (⟨4,V.network.denote⟩ : AnySignature K) ∧ V.network.denote (fun _=>false)≠0 ∧
      (I.NoInteractions V.network.denote ∨ I.minor V.network.denote 0 1≠0) := by
  classical
  by_cases none : I.NoInteractions N.network.denote
  · exact ⟨N,prime,origin,Or.inl none⟩
  · unfold I.NoInteractions at none
    push Not at none
    obtain ⟨i,j,distinct,edge⟩:=none
    refine ⟨O.ordered H N i j,O.prime H N _ prime,O.origin H N _ origin,Or.inr ?_⟩
    rwa [O.ordered_edge H N i j distinct]

inductive Produced : Type where
  | ternary (output : NoXOrdinaryGraphAdjoin.Output H 3)
      (prime : Prime (⟨3,output.network.denote⟩ : AnySignature K))
  | paired (output : NoXOrdinaryGraphAdjoin.Output H 4)
      (support : Q.Paired output.network.denote)
      (nonsingular : Q.determinant output.network.denote≠0)
  | zeroOrigin (output : NoXOrdinaryGraphAdjoin.Output H 3)
      (nonzero : output.network.denote≠0) (zero : output.network.denote (fun _=>false)=0)

theorem large_ternary_leaf (f : Signature K 3) (t : FactorTree (⟨3,f⟩ : AnySignature K))
    (g : AnySignature K) (member : g∈t.leaves) (large : 3≤g.1) :
    Prime (⟨3,f⟩ : AnySignature K) := by
  obtain equal|⟨b,⟨s⟩⟩:=t.leaf_split g member
  · rw [equal]
    exact FactorTree.leaves_prime t g member
  · have small:=s.left_lt
    change g.1<3 at small
    omega

def produce : Produced H := by
  classical
  let e:=exists_order H N prime origin
  let V:=Classical.choose e
  have pv:= (Classical.choose_spec e).1
  have ov:= (Classical.choose_spec e).2.1
  have order:= (Classical.choose_spec e).2.2
  let trees:=Z.tree H U V scalar scalarNonzero pin0 pin1 ov
  by_cases small : ∀i,∀g∈(trees i).leaves,g.1≤2
  · have caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i V.network.denote) := by
      intro i
      exact Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArity.tensorClosure_of_saved_tree
        (Z.liftedTree H U V scalar scalarNonzero pin0 pin1 ov (by decide) i)
        (fun n (_ : Signature K n)=>n≤2)
        (Z.lifted_small H U V scalar scalarNonzero pin0 pin1 ov (by decide) small i)
    have cross : I.minor V.network.denote 0 2=0 ∧ I.minor V.network.denote 0 3=0 ∧
        I.minor V.network.denote 1 2=0 ∧ I.minor V.network.denote 1 3=0 := by
      rcases order with none|edge
      · exact ⟨none 0 2 (by decide),none 0 3 (by decide),none 1 2 (by decide),none 1 3 (by decide)⟩
      · exact Q.cross V.network.denote caps edge
    have q0 : V.network.denote ![false,false,false,false]≠0 := by
      simpa only [show (![false,false,false,false] : Fin 4→Bool)=(fun _=>false) by
        funext j;fin_cases j <;>rfl] using ov
    have form : V.network.denote=fun x=>Q.product V.network.denote x+
        if x=(fun _=>true) then Q.correction V.network.denote else 0 :=
      Q.reconstruct V.network.denote q0 cross.1 cross.2.1 cross.2.2.1 cross.2.2.2
        (Q.cap_cubic H U V scalar scalarNonzero pin0 pin1 ov small)
    by_cases singles : ∀i,V.network.denote (I.single i)=0
    · exact .paired V (Q.paired _ form singles) (Q.nonsingular _ q0 pv form)
    · have some : ∃i,V.network.denote (I.single i)≠0 := by push Not at singles;exact singles
      let i:=Classical.choose some
      have hi:=Classical.choose_spec some
      let W:=M.output H U V i
      have alternative:=M.alternative H U V scalar scalarNonzero pin0 pin1 ov pv form i hi
      by_cases pw : Prime (⟨3,W.network.denote⟩ : AnySignature K)
      · exact .ternary W pw
      · exact .zeroOrigin W (alternative.resolve_left pw).1 (alternative.resolve_left pw).2
  · have found : ∃i,∃g∈(trees i).leaves,3≤g.1 := by
      push Not at small
      obtain ⟨i,g,member,large⟩:=small
      exact ⟨i,g,member,by omega⟩
    let i:=Classical.choose found
    let p:=Classical.choose_spec found
    let g:=Classical.choose p
    have member:= (Classical.choose_spec p).1
    have large:= (Classical.choose_spec p).2
    exact .ternary (Z.output H U V i) (large_ternary_leaf _ (trees i) g member large)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternarySelector
end
