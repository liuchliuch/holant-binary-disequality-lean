import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopTransport
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBitFlipPins
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPortOrder
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryLoopGraph
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOddEquality

/-! Ordinary loops commute with a supported-word mask only at equal mask
bits. These graphs keep all old labels and use ordinary equality; the mask
is retained solely in the exact analytic equation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinLoops
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace F
export GlobalCloseCompletionUnaryBitFlip (value prime_iff tensorClosure_iff)
export GlobalCloseCompletionUnaryBitFlipPins (contract_equal_mask reindex_flip)
end F
namespace O
export GlobalCloseCompletionUnaryPortOrder (output denote)
end O
namespace G
export GlobalCloseCompletionUnaryBinaryLoopGraph (sumPorts swapBlocks order graph denote)
export GlobalCloseCompletionUnaryBinaryLoop (loop)
export GlobalCloseCompletionUnaryPinLoopFactor (block)
end G
namespace E
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint)
export GlobalCloseCompletionUnaryProductTopTransport (zero_weights)
export GlobalCloseCompletionUnaryProductTopPrime (prime)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {r n m : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))

def output (N : NoXOrdinaryGraphAdjoin.Output H (n+2)) : NoXOrdinaryGraphAdjoin.Output H n where
  network:=N.network.contract Signature.equality
  labels:=LabelledNetwork.contract N.network N.labels 0 Signature.equality
  exact:=N.exact
  ordinary e:=Fin.cases rfl (fun e=>N.ordinary e) e

theorem signed_denote (N : NoXOrdinaryGraphAdjoin.Output H (n+2)) (mask : Fin (n+2)→Bool)
    (same : mask 0=mask 1) :
    F.value (fun j=>mask j.succ.succ) (output H N).network.denote=
      Signature.contract Signature.equality (F.value mask N.network.denote) := by
  change F.value _ (N.network.contract Signature.equality).denote=_
  rw [Network.denote_contract]
  have word : mask=Fin.cons (mask 0) (Fin.cons (mask 0) (fun j=>mask j.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun j=>Fin.cases ?_ (fun _=>rfl) j) i
    exact same.symm
  conv_rhs=>rw [word]
  exact (F.contract_equal_mask _ _ _).symm

theorem endpoint_contract (c d : K) :
    Signature.contract Signature.equality (E.endpoint (n+2) c d)=E.endpoint n c d := by
  funext x
  rw [Signature.contract_equality]
  simp [E.endpoint,Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin,
    funext_iff,Fin.forall_fin_succ]

theorem endpoint_prime (N : NoXOrdinaryGraphAdjoin.Output H (n+2)) (mask : Fin (n+2)→Bool)
    (same : mask 0=mask 1) (positive : 0<n) (c d : K) (hc : c≠0) (hd : d≠0)
    (form : F.value mask N.network.denote=E.endpoint (n+2) c d) :
    Prime (⟨n,(output H N).network.denote⟩ : AnySignature K) := by
  apply (F.prime_iff (fun j=>mask j.succ.succ) _).mp
  rw [signed_denote H N mask same,form,endpoint_contract,←E.zero_weights]
  exact E.prime _ c d positive hc hd

theorem block_order (m : ℕ) : G.order (G.sumPorts m)=G.swapBlocks m := by
  ext i
  simp [G.order]

theorem normalized_binary_loop (f : Signature K (m+4)) :
    Signature.contract Signature.equality (Tensor.reindex (G.swapBlocks m) f)=
      G.loop (G.block (G.sumPorts m) f) := by
  have h:=G.denote (G.sumPorts m) (Network.corolla f)
  rw [G.graph,Network.denote_contract] at h
  have eqn : (Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction.reboundary
      (Network.corolla f) (G.order (G.sumPorts m))).denote=Tensor.reindex (G.swapBlocks m) f := by
    funext x
    rw [Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction.reboundary_denote,Network.denote_corolla,block_order]
    rfl
  rw [eqn,Network.denote_corolla] at h
  exact h

def binaryOutput (N : NoXOrdinaryGraphAdjoin.Output H (m+4)) : NoXOrdinaryGraphAdjoin.Output H (m+2) :=
  output H (O.output H N (G.swapBlocks m))

def binaryMask (mask : Fin (m+4)→Bool) : Fin (m+2)→Bool := fun j=>mask (G.swapBlocks m j.succ.succ)

theorem binary_signed_denote (N : NoXOrdinaryGraphAdjoin.Output H (m+4)) (mask : Fin (m+4)→Bool)
    (same : mask 2=mask 3) :
    F.value (binaryMask mask) (binaryOutput H N).network.denote=
      G.loop (G.block (G.sumPorts m) (F.value mask N.network.denote)) := by
  rw [←normalized_binary_loop,F.reindex_flip]
  have h:=signed_denote H (O.output H N (G.swapBlocks m))
    (fun j=>mask ((G.swapBlocks m).symm j)) (show mask ((G.swapBlocks m).symm 0)=mask ((G.swapBlocks m).symm 1) from same)
  rw [O.denote] at h
  exact h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinLoops
end
