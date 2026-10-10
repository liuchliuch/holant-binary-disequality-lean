import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateAlgebra
import Holant.Proofs.FiniteGroups.Stabilization.FactorExposure

/-! Exact three equality joins for a six-port gate and an arbitrary original
row. A finite nine-port permutation exposes all three joins without changing
the order of the untouched boundary ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateCircuit
open Holant Holant.OpenNetworkComposition Holant.LocalDrafts.FinitePGL2.Stabilization
namespace A
export GlobalCloseCompletionKleinH6GateAlgebra (front tail append action sum_three)
end A
namespace D
export GlobalCloseCompletionKleinH6GateData (Word3 join matrix matrix_cast)
end D
namespace H
export GlobalCloseCompletionKleinH6RMBell (core)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def headOrder : Equiv.Perm (Fin 9) where
  toFun := ![6,7,8,0,2,4,1,3,5]
  invFun := ![3,6,4,7,5,8,0,1,2]
  left_inv := by decide
  right_inv := by decide

def extend (n : ℕ) : Equiv.Perm (Fin (9+n)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr headOrder (Equiv.refl (Fin n)))).trans finSumFinEquiv

def order (n : ℕ) : Fin (6+(n+3))≃Fin (n+9) :=
  ((finCongr (by omega : 6+(n+3)=9+n)).trans (extend n)).trans (finCongr (by omega : 9+n=n+9))

theorem order_head (n : ℕ) (j : Fin 9) :
    order n ⟨j.val,by omega⟩=⟨(headOrder j).val,by have h:=(headOrder j).isLt;omega⟩ := by
  change (finCongr (by omega : 9+n=n+9)) (extend n (Fin.castAdd n j))=_
  simp only [extend,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,Equiv.sumCongr_apply,
    finSumFinEquiv_apply_left]
  rfl

theorem order_tail (n : ℕ) (j : Fin n) :
    order n ⟨9+j.val,by omega⟩=⟨9+j.val,by omega⟩ := by
  change (finCongr (by omega : 9+n=n+9)) (extend n (Fin.natAdd 9 j))=_
  simp only [extend,Equiv.trans_apply,finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,
    Equiv.refl_apply,finSumFinEquiv_apply_right]
  rfl

variable {K : Type*} [Field K] {n : ℕ}

def circuit (h : Signature K 6) (f : Signature K (n+3)) : Signature K (n+3) :=
  Signature.contract Signature.equality (Signature.contract Signature.equality
    (Signature.contract Signature.equality (Tensor.reindex (order n) (Signature.tensor h f))))

theorem input (h : Signature K 6) (f : Signature K (n+3)) (x : Fin (n+3)→Bool)
    (a b c d e g : Bool) :
    Tensor.reindex (order n) (Signature.tensor h f)
      (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (Fin.cons e (Fin.cons g x))))))=
      h ![x 0,Fin.tail x 0,Fin.tail (Fin.tail x) 0,a,c,e]*
        f (Fin.cons b (Fin.cons d (Fin.cons g (A.tail x)))) := by
  simp only [Tensor.reindex,Signature.tensor_apply]
  congr 1
  · apply congrArg h
    funext i
    have hi := order_head n (⟨i.val,by omega⟩ : Fin 9)
    change order n (Fin.castAdd (n+3) i)=⟨(headOrder ⟨i.val,by omega⟩).val,by have h:=(headOrder ⟨i.val,by omega⟩).isLt;omega⟩ at hi
    rw [hi]
    fin_cases i <;> rfl
  · apply congrArg f
    funext i
    refine Fin.cases ?_ (fun i=>?_) i
    · have h0 := order_head n (⟨6,by decide⟩ : Fin 9)
      change order n (Fin.natAdd 6 (0 : Fin (n+3)))=⟨1,by omega⟩ at h0
      rw [h0]
      rfl
    · refine Fin.cases ?_ (fun i=>?_) i
      · have h1 := order_head n (⟨7,by decide⟩ : Fin 9)
        change order n (Fin.natAdd 6 (Fin.succ (0 : Fin (n+2))))=⟨3,by omega⟩ at h1
        rw [h1]
        rfl
      · refine Fin.cases ?_ (fun i=>?_) i
        · have h2 := order_head n (⟨8,by decide⟩ : Fin 9)
          change order n (Fin.natAdd 6 (Fin.succ (Fin.succ (0 : Fin (n+1)))))=⟨5,by omega⟩ at h2
          rw [h2]
          rfl
        · have hi : Fin.natAdd 6 (Fin.succ (Fin.succ (Fin.succ i)))=(⟨9+i.val,by omega⟩ : Fin (6+(n+3))) := by
            apply Fin.ext
            simp only [Fin.coe_natAdd,Fin.val_succ]
            omega
          rw [hi,order_tail]
          have hj : (⟨9+i.val,by omega⟩ : Fin (n+9))=i.succ.succ.succ.succ.succ.succ.succ.succ.succ := by
            apply Fin.ext
            simp only [Fin.val_succ]
            omega
          rw [hj]
          rfl

theorem value (h : Signature K 6) (f : Signature K (n+3)) (x : Fin (n+3)→Bool) :
    circuit h f x=∑u : D.Word3,h (D.join (A.front x) u)*f (A.append u (A.tail x)) := by
  simp only [circuit,Signature.contract_equality,input,A.sum_three,Fintype.sum_bool]
  simp only [D.join,A.front,A.append]
  ac_rfl

theorem core_value (f : Signature K (n+3)) : circuit H.core f=A.action false f := by
  funext x
  rw [value]
  simp only [A.action,D.matrix_cast,Bool.false_eq_true,ite_false]

theorem scale_left (h : Signature K 6) (f : Signature K (n+3)) (c : K) :
    circuit (c • h) f=c • circuit h f := by
  funext x
  simp only [value,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem actual (F : SignatureFamily K) (identity : RetainsIdentity F)
    (h : Signature K 6) (actualH : Gadget.Realizes F .disequality h)
    (f : Signature K (n+3)) (actualF : Gadget.Realizes F .disequality f) :
    Gadget.Realizes F .disequality (circuit h f) := by
  have tensor := realizes_tensor F .disequality h f actualH actualF
  have reordered := realizes_reindex_equiv F (order n) (Signature.tensor h f) tensor
  exact GlobalCloseCompletionKleinH6RMActual.equality_contract_actual F identity _
    (GlobalCloseCompletionKleinH6RMActual.equality_contract_actual F identity _
      (GlobalCloseCompletionKleinH6RMActual.equality_contract_actual F identity _ reordered))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateCircuit
end
