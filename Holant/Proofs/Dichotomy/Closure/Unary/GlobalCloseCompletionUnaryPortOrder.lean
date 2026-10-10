import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductInteraction
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.Closure.ClosureShiftedWeightedAncestor
import Holant.Dihedral.CompatibleClosure.PairOrder

/-! Exact original-port reordering for the unary selector. The coefficient
interaction and tensor primality move with the same labelled graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPortOrder
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double)
export GlobalCloseCompletionUnaryPinnedProduct (single)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}

theorem single_word (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (fun j=>I.single i (e j))=I.single (e.symm i) := by
  funext j
  by_cases h : j=e.symm i
  · subst j;simp [I.single]
  · have ne : e j≠i := by intro same;exact h (e.injective (same.trans (e.apply_symm_apply i).symm))
    simp [I.single,Function.update_of_ne h,Function.update_of_ne ne]

theorem double_word (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    (fun k=>I.double i j (e k))=I.double (e.symm i) (e.symm j) := by
  funext k
  by_cases h : k=e.symm j
  · subst k;simp [I.double]
  · have ne : e k≠j := by intro same;exact h (e.injective (same.trans (e.apply_symm_apply j).symm))
    simp only [I.double,Function.update_of_ne h,Function.update_of_ne ne]
    exact congrFun (single_word e i) k

theorem minor_reindex (e : Equiv.Perm (Fin n)) (f : Signature K n) (i j : Fin n) :
    I.minor (Tensor.reindex e f) i j=I.minor f (e.symm i) (e.symm j) := by
  simp only [I.minor,Tensor.reindex,double_word,single_word]

variable (H : (j : Fin r)→Signature K (a j.val)) (N : NoXOrdinaryGraphAdjoin.Output H n)

def output (e : Equiv.Perm (Fin n)) : NoXOrdinaryGraphAdjoin.Output H n where
  network:=reboundary N.network e
  labels:={vertex:=N.labels.vertex,vertex_arity:=N.labels.vertex_arity,edge:=N.labels.edge}
  exact:=N.exact
  ordinary:=N.ordinary

theorem denote (e : Equiv.Perm (Fin n)) : (output H N e).network.denote=Tensor.reindex e N.network.denote := by
  funext x
  exact reboundary_denote N.network e x

theorem prime (e : Equiv.Perm (Fin n)) (hp : Prime (⟨n,N.network.denote⟩ : AnySignature K)) :
    Prime (⟨n,(output H N e).network.denote⟩ : AnySignature K) := by
  rw [denote]
  exact Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureShiftedWeighted.reindex_prime e _ hp

theorem origin (e : Equiv.Perm (Fin n)) (hp : N.network.denote (fun _=>false)≠0) :
    (output H N e).network.denote (fun _=>false)≠0 := by
  simpa only [denote,Tensor.reindex] using hp

variable (N4 : NoXOrdinaryGraphAdjoin.Output H 4)

def ordered (i j : Fin 4) : NoXOrdinaryGraphAdjoin.Output H 4 :=
  output H N4 (Holant.Dihedral.CompatibleClosure.pairOrder i j).symm

theorem ordered_edge (i j : Fin 4) (distinct : i≠j) :
    I.minor (ordered H N4 i j).network.denote 0 1=I.minor N4.network.denote i j := by
  rw [ordered,denote,minor_reindex]
  simp only [Equiv.symm_symm,Holant.Dihedral.CompatibleClosure.pairOrder_first i j distinct,
    Holant.Dihedral.CompatibleClosure.pairOrder_second]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPortOrder
end
