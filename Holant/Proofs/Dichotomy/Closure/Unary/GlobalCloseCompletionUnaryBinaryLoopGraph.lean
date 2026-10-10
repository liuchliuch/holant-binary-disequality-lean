import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryLoopExit
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroOriginSource

/-! The binary-UPF disjoint loop is a real ordinary labelled network.
The selected pair stays at output ports zero and one; the first two
complement ports become one equality edge. Every old vertex is unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryLoopGraph
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
namespace R
export GlobalCloseCompletionUnaryPinLoopFactor (block)
end R
namespace L
export GlobalCloseCompletionUnaryBinaryLoop (loop)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K] {m k r : ℕ} {a : ℕ→ℕ}

def sumPorts (m : ℕ) : (Fin 2 ⊕ Fin (m+2)) ≃ Fin (m+4) where
  toFun
    | .inl i=>if i=0 then ⟨0,by omega⟩ else ⟨1,by omega⟩
    | .inr j=>j.succ.succ
  invFun:=Fin.cases (.inl 0) (Fin.cases (.inl 1) (fun j=>.inr j))
  left_inv p:=by
    cases p with
    | inl i=>fin_cases i <;>rfl
    | inr j=>rfl
  right_inv i:=by
    refine Fin.cases rfl (fun j=>Fin.cases rfl (fun _=>rfl) j) i

def swapBlocksFun (m : ℕ) : Fin (m+4)→Fin (m+4) :=
  Fin.cases ⟨2,by omega⟩ (Fin.cases ⟨3,by omega⟩
    (Fin.cases ⟨0,by omega⟩ (Fin.cases ⟨1,by omega⟩ (fun i=>i.succ.succ.succ.succ))))
theorem swapBlocks_inverse (m : ℕ) (i : Fin (m+4)) : swapBlocksFun m (swapBlocksFun m i)=i := by
  refine Fin.cases rfl (fun j=>Fin.cases rfl (fun l=>Fin.cases rfl (fun q=>Fin.cases rfl (fun _=>rfl) q) l) j) i
def swapBlocks (m : ℕ) : Equiv.Perm (Fin (m+4)) where
  toFun:=swapBlocksFun m
  invFun:=swapBlocksFun m
  left_inv:=swapBlocks_inverse m
  right_inv:=swapBlocks_inverse m

variable (ports : (Fin 2 ⊕ Fin (m+2)) ≃ Fin k) (N : Network K k)
def order : Fin k ≃ Fin (m+4) := ports.symm.trans ((sumPorts m).trans (swapBlocks m))
def graph : Network K (m+2) := (reboundary N (order ports)).contract Signature.equality

theorem denote : (graph ports N).denote=L.loop (R.block ports N.denote) := by
  rw [graph,Network.denote_contract]
  funext x
  rw [Signature.contract_equality]
  simp only [reboundary_denote]
  have words (b : Bool) :
      (fun i=>(Fin.cons b (Fin.cons b x) : Fin (m+4)→Bool) (order ports i))=
        (fun i=>Sum.elim ![x 0,x 1]
          (Fin.cons b (Fin.cons b (fun j=>x j.succ.succ))) (ports.symm i)) := by
    funext i
    simp only [order,Equiv.trans_apply]
    generalize hp : ports.symm i=p
    change (Fin.cons b (Fin.cons b x) : Fin (m+4)→Bool)
      (swapBlocks m (sumPorts m p))=_
    cases p with
    | inl j=>fin_cases j <;>rfl
    | inr j=>refine Fin.cases rfl (fun l=>Fin.cases rfl (fun _=>rfl) l) j
  rw [words false,words true]
  rfl

variable (H : (i : Fin r)→Signature K (a i.val)) (NL : Labelling N.shape r 1 a)
variable (exactN : LabelledNetwork.Exact H N NL) (ordinaryN : ∀e,N.edge e=Signature.equality)

def labels : Labelling (graph ports N).shape r 1 a where
  vertex:=NL.vertex
  vertex_arity:=NL.vertex_arity
  edge:=Fin.cons 0 NL.edge

include exactN in
theorem exact : LabelledNetwork.Exact H (graph ports N) (labels ports N NL) := exactN
include ordinaryN in
theorem ordinary : ∀e,(graph ports N).edge e=Signature.equality := fun e=>Fin.cases rfl ordinaryN e
theorem counts : (graph ports N).shape.vertices=N.shape.vertices ∧
    (graph ports N).shape.edges=N.shape.edges+1 := ⟨rfl,rfl⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryLoopGraph
end
