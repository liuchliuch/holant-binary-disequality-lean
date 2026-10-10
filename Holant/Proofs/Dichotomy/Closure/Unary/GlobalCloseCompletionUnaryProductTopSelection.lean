import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopMarginal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin

/-! Closed all-unary zero-cap selector, including the quaternary base.
The original prime and its actual zero pin are the input resources. Every
normal-form coefficient and marginal is selected inside. The output is an
actual weighted equality, smaller prime, or nonzero opposite-pin power. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopSelection
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (canonical single cap UnaryProduct top_difference_nonzero)
end P
namespace T
export GlobalCloseCompletionUnaryProductTopPrime (value normal_form)
export GlobalCloseCompletionUnaryProductTopTransport (zero_weights)
end T
namespace M
export GlobalCloseCompletionUnaryProductTopMarginal
  (graph labels exact ordinary right right_nonzero pin smaller_or_power)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H (n+1))
variable (large : 3≤n)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (prime : Prime (⟨n+1,N.network.denote⟩ : AnySignature K))
variable (origin : N.network.denote (fun _=>false)≠0)
variable (caps : ∀i,P.UnaryProduct (P.cap i N.network.denote))

def weights : Fin (n+1)→K := fun i=>N.network.denote (P.single i)/N.network.denote (fun _=>false)
def correction : K := N.network.denote (fun _=>true)-P.canonical N.network.denote (fun _=>true)

inductive Produced : Type where
  | endpoint (equation : N.network.denote=GlobalCloseCompletionUnaryOrdinaryEquality.endpoint
      (n+1) (N.network.denote (fun _=>false)) (correction H N))
      (second_nonzero : correction H N≠0)
  | lower (output : NoXOrdinaryGraphAdjoin.Output H n)
      (prime : Prime (⟨n,output.network.denote⟩ : AnySignature K))
  | opposite (output : NoXOrdinaryGraphAdjoin.Output H n) (scale : K) (nonzero : scale≠0)
      (equation : output.network.denote=fun x=>scale*Signature.unaryPower (M.pin (K:=K)) n x)

def produce : Produced H N := by
  classical
  let w:=weights H N
  let c:=N.network.denote (fun _=>false)
  let d:=correction H N
  have form : N.network.denote=T.value w c d := T.normal_form N.network.denote origin caps
  have hd : d≠0 := P.top_difference_nonzero N.network.denote (by omega) prime origin caps
  by_cases nonzero : ∃i,w i≠0
  · let i:=Classical.choose nonzero
    have hi : w i≠0 := Classical.choose_spec nonzero
    let V : NoXOrdinaryGraphAdjoin.Output H n := {
      network:=M.graph U.network N.network i
      labels:=M.labels U.network N.network i H U.labels N.labels U.exact N.exact
      exact:=M.exact U.network N.network i H U.labels N.labels U.exact N.exact
      ordinary:=M.ordinary U.network N.network i U.ordinary N.ordinary }
    have h:=M.smaller_or_power U.network N.network w c d scalar i (by omega) pin0 pin1 form
      scalarNonzero origin hd hi
    by_cases lower : Prime (⟨n,(M.graph U.network N.network i).denote⟩ : AnySignature K)
    · exact .lower V lower
    · exact .opposite V (M.right w c d scalar i)
        (M.right_nonzero w c d scalar i scalarNonzero origin hd hi) (h.resolve_left lower)
  · have allzero : w=(fun _=>0) := by
      funext i
      by_contra hi
      exact nonzero ⟨i,hi⟩
    have endpoint:=form
    rw [allzero,T.zero_weights] at endpoint
    exact .endpoint endpoint hd

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopSelection
end
