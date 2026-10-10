import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPrimeSubgraph
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternarySelector
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOddEquality

/-! The universal prime selector uses actual zero caps, actual ordinary
loops, and strict arity descent. Every retained cap factor is physically
isolated with the same zero pin. The closed result is an actual ternary
prime, an actual nonsingular paired quaternary, or an actual nonzero
zero-origin tensor. It neither selects the harmless old Z row nor assumes
any independent-unary hardness theorem. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryUniversalSelector
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace High
export GlobalCloseCompletionUnaryHighSelector (select leaf_arity_le)
end High
namespace Q
export GlobalCloseCompletionUnaryQuaternarySelector (produce)
export GlobalCloseCompletionUnaryQuaternaryForm (Paired determinant)
end Q
namespace Z
export GlobalCloseCompletionUnaryZeroCapTrees (output value tree permutation)
end Z
namespace F
export GlobalCloseCompletionUnaryFactorCaps (exists_leaf)
export GlobalCloseCompletionUnaryPrimeSubgraph (exists_prime nonzero_of_nonsmall)
end F
namespace E
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint)
export GlobalCloseCompletionUnaryOddEquality (contract_denote)
export GlobalCloseCompletionUnaryProductTopPrime (prime)
export GlobalCloseCompletionUnaryProductTopTransport (zero_weights)
end E
namespace M
export GlobalCloseCompletionUnaryProductTopMarginal (pin)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))

inductive Produced : Type where
  | ternary (output : NoXOrdinaryGraphAdjoin.Output H 3)
      (prime : Prime (⟨3,output.network.denote⟩ : AnySignature K))
  | paired (output : NoXOrdinaryGraphAdjoin.Output H 4)
      (support : Q.Paired output.network.denote)
      (nonsingular : Q.determinant output.network.denote≠0)
  | zeroOrigin {n : ℕ} (output : NoXOrdinaryGraphAdjoin.Output H n) (positive : 0<n)
      (nonzero : output.network.denote≠0) (zero : output.network.denote (fun _=>false)=0)

variable (U : NoXOrdinaryGraphAdjoin.Output H 1)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)

include scalarNonzero pin0 pin1 in
theorem cap_origin {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H (n+1))
    (origin : N.network.denote (fun _=>false)≠0) (i : Fin (n+1)) :
    (Z.output H U N i).network.denote (fun _=>false)≠0 := by
  change (GlobalCloseCompletionUnaryZeroCapTrees.graph H U N i).denote (fun _=>false)≠0
  rw [Z.value H U N scalar pin0 pin1 i]
  have word : (fun j=>(Fin.cons false (fun _ : Fin n=>false) : Fin (n+1)→Bool) (Z.permutation i j))=(fun _=>false) := by
    funext j
    generalize Z.permutation i j=k
    exact Fin.cases rfl (fun _=>rfl) k
  rw [word]
  exact mul_ne_zero scalarNonzero origin

def loop {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H (n+2)) : NoXOrdinaryGraphAdjoin.Output H n where
  network:=N.network.contract Signature.equality
  labels:=LabelledNetwork.contract N.network N.labels 0 Signature.equality
  exact:=N.exact
  ordinary e:=Fin.cases rfl (fun e=>N.ordinary e) e

theorem endpoint_loop_prime {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H (n+2))
    (positive : 0<n) (A B : K) (ha : A≠0) (hb : B≠0)
    (form : N.network.denote=E.endpoint (n+2) A B) :
    Prime (⟨n,(loop H N).network.denote⟩ : AnySignature K) := by
  change Prime (⟨n,(N.network.contract Signature.equality).denote⟩ : AnySignature K)
  rw [E.contract_denote N.network A B form,←E.zero_weights]
  exact E.prime _ A B positive ha hb

theorem opposite_nonzero {n : ℕ} (f : Signature K n) (c : K) (hc : c≠0)
    (form : f=fun x=>c*Signature.unaryPower (M.pin (K:=K)) n x) : f≠0 := by
  intro zero
  have h:=congrFun zero (fun _=>true)
  rw [form] at h
  exact hc (by simpa [Signature.unaryPower,M.pin] using h)

theorem opposite_origin {n : ℕ} (positive : 0<n) (f : Signature K n) (c : K)
    (form : f=fun x=>c*Signature.unaryPower (M.pin (K:=K)) n x) : f (fun _=>false)=0 := by
  rw [form]
  simp [Signature.unaryPower,M.pin,positive.ne']

include scalarNonzero pin0 pin1 in
theorem exists_produced (n : ℕ) (N : NoXOrdinaryGraphAdjoin.Output H n)
    (large : 3≤n) (prime : Prime (⟨n,N.network.denote⟩ : AnySignature K)) :
    Nonempty (Produced H) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih=>
    by_cases origin : N.network.denote (fun _=>false)≠0
    · by_cases three : n=3
      · subst n
        exact ⟨.ternary N prime⟩
      by_cases four : n=4
      · subst n
        cases Q.produce H U N scalar scalarNonzero pin0 pin1 prime origin with
        | ternary V pv=>exact ⟨.ternary V pv⟩
        | paired V support det=>exact ⟨.paired V support det⟩
        | zeroOrigin V nonzero zero=>exact ⟨.zeroOrigin V (by decide) nonzero zero⟩
      obtain ⟨m,rfl⟩ : ∃m,n=m+4 := ⟨n-4,by omega⟩
      have positive : 0<m := by omega
      cases High.select H U N positive scalar scalarNonzero pin0 pin1 prime origin with
      | capFactor i factor member nonbinary=>
        let V:=Z.output H U N i
        have live:=cap_origin H U scalar scalarNonzero pin0 pin1 N origin i
        obtain ⟨W,pw,ow,c,hc,form⟩:=F.exists_leaf H U V scalar scalarNonzero pin0 pin1 live
          (Z.tree H U N scalar scalarNonzero pin0 pin1 origin i) factor member
        have bound:=High.leaf_arity_le (Z.tree H U N scalar scalarNonzero pin0 pin1 origin i) member
        change factor.1≤m+3 at bound
        exact ih factor.1 (by omega) W nonbinary pw
      | unary result=>
        cases result with
        | endpoint form second=>
          exact ih (m+2) (by omega) (loop H N) (by omega)
            (endpoint_loop_prime H N (by omega) _ _ origin second form)
        | lower V pv=>exact ih (m+3) (by omega) V (by omega) pv
        | opposite V c hc form=>
          exact ⟨.zeroOrigin V (by omega) (opposite_nonzero _ c hc form)
            (opposite_origin (by omega) _ c form)⟩
      | loop V alternative=>
        rcases alternative with nonsmall|⟨nonzero,zero⟩
        · by_cases live : V.network.denote (fun _=>false)≠0
          · obtain ⟨k,big,bound,W,pw,ow⟩:=F.exists_prime H U V scalar scalarNonzero pin0 pin1 live nonsmall
            exact ih k (by omega) W big pw
          · exact ⟨.zeroOrigin V (by omega) (F.nonzero_of_nonsmall (by omega) _ nonsmall) (not_not.mp live)⟩
        · exact ⟨.zeroOrigin V (by omega) nonzero zero⟩
    · exact ⟨.zeroOrigin N (by omega) prime.1 (not_not.mp origin)⟩

def produce (n : ℕ) (N : NoXOrdinaryGraphAdjoin.Output H n)
    (large : 3≤n) (prime : Prime (⟨n,N.network.denote⟩ : AnySignature K)) : Produced H :=
  Classical.choice (exists_produced H U scalar scalarNonzero pin0 pin1 n N large prime)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryUniversalSelector
end
