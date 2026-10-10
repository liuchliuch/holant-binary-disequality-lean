import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroCaps

/-! Exact original-port permutation and actual unary attachment for the
two-product form. The attachment handles the arity-four selector base case
as well as higher arities, retaining the real unary marginal multiplier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopTransport
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
open scoped BigOperators
namespace T
export GlobalCloseCompletionUnaryProductTopPrime (value)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

theorem reindex (w : Fin n→K) (c d : K) (e : Equiv.Perm (Fin n)) :
    Tensor.reindex e (T.value w c d)=T.value (fun i=>w (e.symm i)) c d := by
  classical
  funext x
  have top : (fun i=>x (e i))=(fun _=>true) ↔ x=(fun _=>true) := by
    constructor
    · intro h
      funext j
      simpa only [Equiv.apply_symm_apply] using congrFun h (e.symm j)
    · rintro rfl
      rfl
  have prod : (∏i,if x (e i) then w i else 1)=∏i,if x i then w (e.symm i) else 1 := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp e (fun i=>if x i then w (e.symm i) else 1))
  simp only [Tensor.reindex,T.value,top,prod]

theorem reboundary (N : Network K n) (w : Fin n→K) (c d : K)
    (form : N.denote=T.value w c d) (e : Equiv.Perm (Fin n)) :
    (Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction.reboundary N e).denote=
      T.value (fun i=>w (e.symm i)) c d := by
  have eqn : (Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction.reboundary N e).denote=
      Tensor.reindex e N.denote := funext fun x=>reboundary_denote N e x
  rw [eqn,form,reindex]

theorem attach (U : Network K 1) (N : Network K (n+1))
    (w : Fin (n+1)→K) (c d scalar a : K)
    (unary : U.denote=fun x=>scalar*(if x 0 then a else 1))
    (form : N.denote=T.value w c d) :
    (capHead U N).denote=T.value (fun i=>w i.succ) (scalar*c*(1+a*w 0)) (scalar*d*a) := by
  classical
  funext x
  rw [capHead_denote,unary,form]
  simp only [T.value,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,ite_false,ite_true,
    funext_iff,Fin.forall_fin_succ,Bool.false_eq_true,false_and,true_and,one_mul,mul_one]
  split_ifs <;> ring

/-- With every unary coordinate zero the form is already weighted equality,
so the existing actual endpoint consumer applies directly. -/
theorem zero_weights (c d : K) : T.value (fun _ : Fin n=>0) c d=
    GlobalCloseCompletionUnaryOrdinaryEquality.endpoint n c d := by
  classical
  funext x
  simp only [T.value,GlobalCloseCompletionUnaryOrdinaryEquality.endpoint,
    Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.purePin,Pi.add_apply]
  have product : (∏i : Fin n,if x i then (0 : K) else 1)=if x=(fun _=>false) then 1 else 0 := by
    have same : (fun i : Fin n=>if x i then (0 : K) else 1)=
        (fun i=>if x i=false then 1 else 0) := by
      funext i
      cases x i <;> rfl
    rw [show (∏i : Fin n,if x i then (0 : K) else 1)=∏i,if x i=false then (1 : K) else 0 from congrArg (fun f=>∏i,f i) same,
      Fintype.prod_boole]
    simp only [←funext_iff]
  rw [product]
  split_ifs <;> ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopTransport
end
