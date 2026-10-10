import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinCapTrees
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinNormalized
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinLoops
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinPortChoice
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinProductTop

/-! The no-interaction branch of the actual minimal prime cannot have high
arity. A surviving product weight yields a smaller prime by a literal pin1
relative to the supported word. Otherwise the signed endpoint admits an
ordinary equality loop at two equal mask bits, again preserving a prime. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinHighUnary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace D
export GlobalCloseCompletionUnaryBothPinNormalized (Data)
end D
namespace M
export GlobalCloseCompletionUnaryBothPinMinimal (arity least)
end M
namespace C
export GlobalCloseCompletionUnaryBothPinCapTrees (capTree capTree_small)
end C
namespace P
export GlobalCloseCompletionUnaryBothPinProjection (output signed_prime)
export GlobalCloseCompletionUnaryPinnedProduct (canonical single top_difference_nonzero)
export GlobalCloseCompletionUnaryNoInteractionCaps (unary_caps)
export GlobalCloseCompletionUnaryNoInteractions (NoInteractions)
end P
namespace T
export GlobalCloseCompletionUnaryProductTopPrime (value normal_form)
export GlobalCloseCompletionUnaryProductTopTransport (zero_weights reindex)
export GlobalCloseCompletionUnaryBothPinProductTop (oneCap one_cap_prime)
end T
namespace E
export GlobalCloseCompletionUnaryBothPinLoops (output endpoint_prime)
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1)
variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
variable (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient L H))

include pinsForm negative in
theorem impossible {t : ℕ} (positive : 0<t) (N : D.Data H (t+4))
    (size : t+4=M.arity L H pins pinsForm negative) (none : P.NoInteractions N.value) : False := by
  classical
  have bound : t+3<M.arity L H pins pinsForm negative := by omega
  let trees:=C.capTree L H pins pinsForm negative N.actual bound N.mask N.origin (by omega : 0<t+3)
  have tiny : ∀i,∀g∈(trees i).leaves,g.1≤2 :=
    C.capTree_small L H pins pinsForm negative N.actual bound N.mask N.origin (by omega)
  have unary:=P.unary_caps N.value N.origin none trees tiny
  let w:=fun i=>N.value (P.single i)/N.value (fun _=>false)
  let c:=N.value (fun _=>false)
  let d:=N.value (fun _=>true)-P.canonical N.value (fun _=>true)
  have hc : c≠0:=N.origin
  have hd : d≠0:=P.top_difference_nonzero N.value (by omega) N.value_prime N.origin unary
  have form : N.value=T.value w c d:=T.normal_form N.value N.origin unary
  have weights : w=(fun _=>0) := by
    funext i
    by_contra wi
    have smallPrime : Prime (⟨t+3,T.oneCap N.value i⟩ : AnySignature L) := by
      rw [form]
      exact T.one_cap_prime w c d i (by omega) hc hd wi
    have actualPrime:=P.signed_prime H pins pinsForm N.actual N.mask i true smallPrime
    have min:=M.least L H pins pinsForm negative (t+3) (by omega)
      (P.output H pins N.actual i (true^^N.mask i)) actualPrime
    omega
  rw [weights,T.zero_weights] at form
  obtain ⟨i,j,different,same⟩:=GlobalCloseCompletionUnaryBothPinPortChoice.equal_pair N.mask (by omega)
  let e:=Holant.Dihedral.CompatibleClosure.pairOrder i j
  let V:=N.reindex e
  have sameFront : V.mask 0=V.mask 1 := by
    change N.mask (e 0)=N.mask (e 1)
    rw [Holant.Dihedral.CompatibleClosure.pairOrder_first i j different,
      Holant.Dihedral.CompatibleClosure.pairOrder_second]
    exact same
  have vForm : V.value=E.endpoint (t+4) c d := by
    rw [show V.value=Tensor.reindex e.symm N.value from N.reindex_value e,form,←T.zero_weights,T.reindex]
  have prime:=E.endpoint_prime H V.actual V.mask sameFront (by omega : 0<t+2) c d hc hd vForm
  have min:=M.least L H pins pinsForm negative (t+2) (by omega) (E.output H V.actual) prime
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinHighUnary
end
