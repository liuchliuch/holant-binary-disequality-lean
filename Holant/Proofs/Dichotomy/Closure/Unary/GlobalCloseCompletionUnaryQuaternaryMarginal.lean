import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryCapCubic
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryForm
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopMarginal

/-! The quaternary UPF marginal branch is a labelled graph made from two
copies of the actual row and three actual zero pins. A nonzero singleton
coefficient produces a ternary prime or a nonzero tensor with zero origin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryMarginal
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
namespace M
export GlobalCloseCompletionUnaryProductTopMarginal (lastPerm firstPerm atLast atFirst marginal graph labels exact ordinary)
end M
namespace Q
export GlobalCloseCompletionUnaryQuaternaryForm (left right normalized_origin correction_nonzero)
export GlobalCloseCompletionUnaryQuaternaryProductTop (product correction)
end Q
namespace C
export GlobalCloseCompletionUnaryQuaternaryCapCubic (capped value alternative)
end C
namespace Z
export GlobalCloseCompletionUnaryZeroCaps (kept entry)
end Z
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (single)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable (H : (j : Fin r)→Signature K (a j.val))
variable (U : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H 4)
variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : U.network.denote (fun _=>false)=scalar)
variable (pin1 : U.network.denote (fun _=>true)=0)
variable (origin : N.network.denote (fun _=>false)≠0)

def multiplier : K := scalar^3*N.network.denote (fun _=>false)
def ratio (i : Fin 4) : K := N.network.denote (P.single i)/N.network.denote (fun _=>false)

theorem kept_word (i : Fin 4) (b : Bool) :
    (fun j=>Z.kept 3 b (M.lastPerm i j))=(if b then P.single i else fun _=>false) := by
  fin_cases i <;>cases b <;>funext j <;>fin_cases j <;>rfl

include pin0 pin1 origin in
theorem marginal_value (i : Fin 4) : (M.marginal U.network N.network i).denote=
    fun x=>multiplier H N scalar*(if x 0 then ratio H N i else 1) := by
  funext x
  rw [M.marginal,Z.entry U.network scalar pin0 pin1,M.atLast,reboundary_denote]
  change scalar^3*N.network.denote (fun j=>Z.kept 3 (x 0) (M.lastPerm i j))=_
  rw [kept_word]
  cases x 0 <;>simp [multiplier,ratio]
  field_simp [origin]

def output (i : Fin 4) : NoXOrdinaryGraphAdjoin.Output H 3 :=
  ⟨M.graph U.network N.network i,M.labels U.network N.network i H U.labels N.labels U.exact N.exact,
    M.exact U.network N.network i H U.labels N.labels U.exact N.exact,
    M.ordinary U.network N.network i U.ordinary N.ordinary⟩

include pin0 pin1 origin in
theorem denote (i : Fin 4) : (output H U N i).network.denote=
    fun x=>multiplier H N scalar*C.capped N.network.denote i (ratio H N i) x := by
  funext x
  change (M.graph U.network N.network i).denote x=_
  rw [M.graph,capHead_denote,marginal_value H U N scalar pin0 pin1 origin i]
  simp only [Bool.false_eq_true,ite_false,ite_true,mul_one,M.atFirst,reboundary_denote,M.firstPerm,C.capped]
  ring

theorem form_value (f : Signature K 4)
    (form : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0) :
    f=C.value (Q.left f) (Q.right f) (Q.correction f) := by
  funext x
  have h:=congrFun form x
  simpa [C.value,Q.left,Q.right,Q.product,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

include scalarNonzero pin0 pin1 origin in
theorem alternative (prime : Prime (⟨4,N.network.denote⟩ : AnySignature K))
    (form : N.network.denote=fun x=>Q.product N.network.denote x+
      if x=(fun _=>true) then Q.correction N.network.denote else 0)
    (i : Fin 4) (singletonNonzero : N.network.denote (P.single i)≠0) :
    Prime (⟨3,(output H U N i).network.denote⟩ : AnySignature K) ∨
      ((output H U N i).network.denote≠0 ∧ (output H U N i).network.denote (fun _=>false)=0) := by
  have q0 : N.network.denote ![false,false,false,false]≠0 := by
    simpa only [show (![false,false,false,false] : Fin 4→Bool)=(fun _=>false) by
      funext j;fin_cases j <;>rfl] using origin
  have ha : Q.left N.network.denote false false≠0 := by rw [Q.normalized_origin _ q0];exact one_ne_zero
  have hb : Q.right N.network.denote false false≠0 := q0
  have hs : multiplier H N scalar≠0 := mul_ne_zero (pow_ne_zero 3 scalarNonzero) origin
  have hi : ratio H N i≠0 := div_ne_zero singletonNonzero origin
  have h:=C.alternative (Q.left N.network.denote) (Q.right N.network.denote)
    (Q.correction N.network.denote) (ratio H N i) (multiplier H N scalar) ha hb
    (Q.correction_nonzero _ prime form) hi hs i
  rw [←form_value _ form] at h
  simpa only [denote H U N scalar pin0 pin1 origin i] using h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryMarginal
end
