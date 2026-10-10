import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroCapTrees
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryHigh
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopSelection
import Holant.Proofs.Closure.ClosureSmallArity

/-! All high prime rows are dispatched from their actual zero-cap graphs.
Saved factor trees are selected internally. A large cap leaf retains its
precise graph carrier; otherwise the coefficient test selects the proved
unary-product or binary-interaction graph producer. No supplied classifier
or preselected good row enters the selector. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryHighSelector
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Z
export GlobalCloseCompletionUnaryZeroCapTrees (tree output liftedTree lifted_small)
end Z
namespace Top
export GlobalCloseCompletionUnaryProductTopSelection (Produced produce)
end Top
namespace B
export GlobalCloseCompletionUnaryBinaryHigh (exists_step)
end B
namespace I
export GlobalCloseCompletionUnaryNoInteractions (NoInteractions)
export GlobalCloseCompletionUnaryNoInteractionCaps (unary_caps)
export GlobalCloseCompletionUnaryPinnedProduct (cap)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {r m : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H (m+4))
variable (positive : 0<m)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (prime : Prime (⟨m+4,N.network.denote⟩ : AnySignature K))
variable (origin : N.network.denote (fun _=>false)≠0)

abbrev trees := Z.tree H U N scalar scalarNonzero pin0 pin1 origin

inductive Selected : Type where
  | capFactor (i : Fin (m+4)) (factor : AnySignature K)
      (retained : factor∈(trees H U N scalar scalarNonzero pin0 pin1 origin i).leaves)
      (nonbinary : 3≤factor.1)
  | unary (result : Top.Produced H N)
  | loop (output : NoXOrdinaryGraphAdjoin.Output H (m+2))
      (alternative : ¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) output.network.denote ∨
        (output.network.denote≠0 ∧ output.network.denote (fun _=>false)=0))

def select : Selected H U N scalar scalarNonzero pin0 pin1 origin := by
  classical
  by_cases small : ∀i,∀g∈(trees H U N scalar scalarNonzero pin0 pin1 origin i).leaves,g.1≤2
  · let T:=Z.liftedTree H U N scalar scalarNonzero pin0 pin1 origin (by omega : 0<m+3)
    have tiny : ∀i,∀g∈(T i).leaves,g.1≤2 :=
      Z.lifted_small H U N scalar scalarNonzero pin0 pin1 origin (by omega) small
    by_cases none : I.NoInteractions N.network.denote
    · have unaries:=I.unary_caps N.network.denote origin none T tiny
      exact .unary (Top.produce H U N (by omega) scalar scalarNonzero pin0 pin1 prime origin unaries)
    · have interaction : ∃i j : Fin (m+4),i≠j ∧
          GlobalCloseCompletionUnaryProductInteraction.minor N.network.denote i j≠0 := by
        unfold I.NoInteractions at none
        push Not at none
        exact none
      have caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i N.network.denote) := by
        intro i
        exact Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArity.tensorClosure_of_saved_tree
          (T i) (fun n (_ : Signature K n)=>n≤2) (tiny i)
      let h:=B.exists_step H N positive prime origin caps interaction
      exact .loop (Classical.choose h) (Classical.choose_spec h).1
  · have found : ∃i,∃g∈(trees H U N scalar scalarNonzero pin0 pin1 origin i).leaves,3≤g.1 := by
      push Not at small
      obtain ⟨i,g,hg,hlarge⟩:=small
      exact ⟨i,g,hg,by omega⟩
    let i:=Classical.choose found
    let hg:=Classical.choose_spec found
    exact .capFactor i (Classical.choose hg) (Classical.choose_spec hg).1 (Classical.choose_spec hg).2

theorem leaf_arity_le {f g : AnySignature K} (t : FactorTree f) (member : g∈t.leaves) : g.1≤f.1 := by
  induction t with
  | leaf f prime=>
    have h : g=f := by simpa only [FactorTree.leaves,Multiset.mem_singleton] using member
    rw [h]
  | split s a b ia ib=>
    rcases Multiset.mem_add.mp member with left|right
    · exact (ia left).trans s.left_lt.le
    · exact (ib right).trans s.right_lt.le

theorem cap_factor (i : Fin (m+4)) (f : AnySignature K)
    (member : f∈(trees H U N scalar scalarNonzero pin0 pin1 origin i).leaves) :
    Prime f ∧ f.1<m+4 := by
  exact ⟨FactorTree.leaves_prime _ f member,
    lt_of_le_of_lt (leaf_arity_le _ member) (by change m+3<m+4;omega)⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryHighSelector
end
