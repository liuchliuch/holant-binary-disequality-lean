import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryLoopGraph
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryCaps
import Holant.Dihedral.CompatibleClosure.PairOrder
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! Actual high-arity binary-UPF selector. A nonzero anchored binary minor
internally fixes the binary factor and all cap equations. The selected
disjoint ordinary loop is a labelled old-family graph and must expose a
non-small tensor or a nonzero zero-origin resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryHigh
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace C
export GlobalCloseCompletionUnaryBinaryCaps (factor factor_origin factor_det columns first second)
end C
namespace G
export GlobalCloseCompletionUnaryBinaryLoopGraph (sumPorts graph labels exact ordinary denote)
end G
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor)
export GlobalCloseCompletionUnaryPinnedProduct (cap)
end I
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] {m k r : ℕ} {a : ℕ→ℕ}

theorem step (ports : (Fin 2 ⊕ Fin (m+2)) ≃ Fin k) (N : Network K k)
    (positive : 0<m) (prime : Prime (⟨k,N.denote⟩ : AnySignature K))
    (origin : N.denote (fun _=>false)≠0)
    (edge : I.minor N.denote (C.first ports) (C.second ports)≠0)
    (caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i N.denote)) :
    ¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (G.graph ports N).denote ∨
      ((G.graph ports N).denote≠0 ∧ (G.graph ports N).denote (fun _=>false)=0) := by
  have h:=GlobalCloseCompletionUnaryBinaryLoopExit.exit ports N.denote prime positive
    (C.factor ports N.denote) (by rw [C.factor_origin ports N.denote origin];exact one_ne_zero)
    (by rw [C.factor_det ports N.denote origin];exact div_ne_zero edge (pow_ne_zero 2 origin))
    (C.columns ports N.denote origin edge caps)
  simpa only [G.denote] using h

def ports (i j : Fin (m+4)) : (Fin 2 ⊕ Fin (m+2)) ≃ Fin (m+4) :=
  (G.sumPorts m).trans (Holant.Dihedral.CompatibleClosure.pairOrder i j)

theorem first (i j : Fin (m+4)) (different : i≠j) : C.first (ports i j)=i :=
  Holant.Dihedral.CompatibleClosure.pairOrder_first i j different
theorem second (i j : Fin (m+4)) : C.second (ports i j)=j :=
  Holant.Dihedral.CompatibleClosure.pairOrder_second i j

variable (H : (v : Fin r)→Signature K (a v.val))
variable (N : NoXOrdinaryGraphAdjoin.Output H (m+4)) (positive : 0<m)
variable (prime : Prime (⟨m+4,N.network.denote⟩ : AnySignature K))
variable (origin : N.network.denote (fun _=>false)≠0)
variable (caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i N.network.denote))
variable (interaction : ∃i j : Fin (m+4),i≠j ∧ I.minor N.network.denote i j≠0)

include positive prime origin caps interaction in
theorem exists_step : ∃V : NoXOrdinaryGraphAdjoin.Output H (m+2),
    (¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) V.network.denote ∨
      (V.network.denote≠0 ∧ V.network.denote (fun _=>false)=0)) ∧
      V.network.shape.vertices=N.network.shape.vertices ∧
      V.network.shape.edges=N.network.shape.edges+1 := by
  obtain ⟨i,j,different,edge⟩:=interaction
  let V : NoXOrdinaryGraphAdjoin.Output H (m+2) := {
    network:=G.graph (ports i j) N.network
    labels:=G.labels (ports i j) N.network N.labels
    exact:=G.exact (ports i j) N.network H N.labels N.exact
    ordinary:=G.ordinary (ports i j) N.network N.ordinary }
  refine ⟨V,?_,rfl,rfl⟩
  apply step (ports i j) N.network positive prime origin _ caps
  rwa [first i j different,second i j]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryHigh
end
