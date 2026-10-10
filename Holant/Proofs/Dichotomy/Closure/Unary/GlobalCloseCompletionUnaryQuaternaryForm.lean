import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryQuaternaryProductTop

/-! The quaternary correction cannot vanish for a prime tensor. If its
four singleton coefficients vanish, the exact reconstructed row has paired
support and a nonsingular compressed matrix. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryForm
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Q
export GlobalCloseCompletionUnaryQuaternaryProductTop (product correction reconstruct cap)
end Q
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (single)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K]

def left (f : Signature K 4) (u v : Bool) : K := f ![u,v,false,false]/f ![false,false,false,false]
def right (f : Signature K 4) (u v : Bool) : K := f ![false,false,u,v]

def split (f : Signature K 4)
    (form : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0)
    (zero : Q.correction f=0) : ProperSplit (⟨4,f⟩ : AnySignature K)
      ⟨2,fun x=>left f (x 0) (x 1)⟩ ⟨2,fun x=>right f (x 0) (x 1)⟩ where
  left_pos:=by change 0<2;decide
  right_pos:=by change 0<2;decide
  ports:=finSumFinEquiv
  scale:=1
  equation:=by
    funext x
    change f x=1*(left f (x 0) (x 1)*right f (x 2) (x 3))
    have h:=congrFun form x
    simp only [zero,ite_self,add_zero] at h
    simpa [Q.product,left,right,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using h

theorem correction_nonzero (f : Signature K 4)
    (prime : Prime (⟨4,f⟩ : AnySignature K))
    (form : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0) :
    Q.correction f≠0 := by
  intro zero
  exact prime.2 ⟨_,_,⟨split f form zero⟩⟩

theorem normalized_origin (f : Signature K 4) (origin : f ![false,false,false,false]≠0) :
    left f false false=1 := div_self origin

def Paired (f : Signature K 4) : Prop := ∀x,(x 0≠x 1 ∨ x 2≠x 3)→f x=0

def determinant (f : Signature K 4) : K :=
  f ![false,false,false,false]*f ![true,true,true,true]-
    f ![false,false,true,true]*f ![true,true,false,false]

theorem paired (f : Signature K 4)
    (form : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0)
    (singles : ∀i,f (P.single i)=0) : Paired f := by
  have h0 : f ![true,false,false,false]=0 := by
    have hi : P.single (0 : Fin 4)=![true,false,false,false] := by
      funext j;fin_cases j <;>decide
    simpa only [hi] using singles 0
  have h1 : f ![false,true,false,false]=0 := by
    have hi : P.single (1 : Fin 4)=![false,true,false,false] := by
      funext j;fin_cases j <;>decide
    simpa only [hi] using singles 1
  have h2 : f ![false,false,true,false]=0 := by
    have hi : P.single (2 : Fin 4)=![false,false,true,false] := by
      funext j;fin_cases j <;>decide
    simpa only [hi] using singles 2
  have h3 : f ![false,false,false,true]=0 := by
    have hi : P.single (3 : Fin 4)=![false,false,false,true] := by
      funext j;fin_cases j <;>decide
    simpa only [hi] using singles 3
  intro x mismatch
  have h:=congrFun form x
  have hx : x=![x 0,x 1,x 2,x 3] := by funext i;fin_cases i <;>rfl
  rw [hx] at h mismatch ⊢
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;> cases hx3 : x 3 <;>
    simp [hx0,hx1,hx2,hx3,Q.product,h0,h1,h2,h3,funext_iff,Fin.forall_fin_succ] at h mismatch ⊢ <;>exact h

theorem determinant_value (f : Signature K 4) (origin : f ![false,false,false,false]≠0)
    (form : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0) :
    determinant f=f ![false,false,false,false]*Q.correction f := by
  have h:=congrFun form ![true,true,true,true]
  simp only [Q.product,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    funext_iff,Fin.forall_fin_succ] at h
  norm_num at h
  unfold determinant
  rw [h]
  field_simp [origin]
  <;>ring

theorem nonsingular (f : Signature K 4) (origin : f ![false,false,false,false]≠0)
    (prime : Prime (⟨4,f⟩ : AnySignature K))
    (form : f=fun x=>Q.product f x+if x=(fun _=>true) then Q.correction f else 0) :
    determinant f≠0 := by
  rw [determinant_value f origin form]
  exact mul_ne_zero origin (correction_nonzero f prime form)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryForm
end
