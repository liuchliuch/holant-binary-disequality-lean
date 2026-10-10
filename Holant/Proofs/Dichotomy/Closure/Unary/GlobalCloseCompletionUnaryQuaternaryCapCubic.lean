import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryTernaryProductTop
import Mathlib.Tactic.LinearCombination

/-! Every nonzero marginal coordinate of a two-binary-block quaternary
plus top correction yields a ternary prime or a genuine zero-origin tensor.
The proof keeps all coefficients: its cubic is a*correction*origin^2. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryCapCubic
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
namespace C
export GlobalCloseCompletionUnaryTernarySmallCubic (cubic scale)
export GlobalCloseCompletionUnaryTernaryProductTop (prime_of_cubic)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K]

def value (A B : Bool→Bool→K) (d : K) : Signature K 4 :=
  fun x=>A (x 0) (x 1)*B (x 2) (x 3)+if x=(fun _=>true) then d else 0
def capped (f : Signature K 4) (i : Fin 4) (a : K) : Signature K 3 :=
  fun x=>f (fun j=>(Fin.cons false x : Fin 4→Bool) ((Equiv.swap 0 i) j))+
    a*f (fun j=>(Fin.cons true x : Fin 4→Bool) ((Equiv.swap 0 i) j))

theorem cubic (A B : Bool→Bool→K) (d a : K) (i : Fin 4) :
    C.cubic (capped (value A B d) i a)=
      a*d*(capped (value A B d) i a (fun _=>false))^2 := by
  have z : (Fin.cons false (fun _ : Fin 3=>false) : Fin 4→Bool)=![false,false,false,false] := by
    funext j;fin_cases j <;>rfl
  have o : (Fin.cons true (fun _ : Fin 3=>false) : Fin 4→Bool)=![true,false,false,false] := by
    funext j;fin_cases j <;>rfl
  fin_cases i <;>
    simp [C.cubic,capped,value,z,o,funext_iff,Fin.forall_fin_succ,Equiv.swap_apply_def] <;>ring

theorem nonzero (A B : Bool→Bool→K) (d a : K)
    (ha : A false false≠0) (hb : B false false≠0) (hd : d≠0) (harg : a≠0) (i : Fin 4) :
    capped (value A B d) i a≠0 := by
  intro zero
  have ht:=congrFun zero ![true,true,true]
  have h0:=congrFun zero ![true,false,false]
  have h1:=congrFun zero ![false,true,false]
  have h2:=congrFun zero ![false,false,true]
  fin_cases i
  · simp [capped,value,funext_iff,Fin.forall_fin_succ,Equiv.swap_apply_def] at ht h0
    have bad : a*d*B false false=0 := by linear_combination (B false false)*ht-(B true true)*h0
    exact mul_ne_zero (mul_ne_zero harg hd) hb bad
  · simp [capped,value,funext_iff,Fin.forall_fin_succ,Equiv.swap_apply_def] at ht h0
    have bad : a*d*B false false=0 := by linear_combination (B false false)*ht-(B true true)*h0
    exact mul_ne_zero (mul_ne_zero harg hd) hb bad
  · simp [capped,value,funext_iff,Fin.forall_fin_succ,Equiv.swap_apply_def] at ht h2
    have bad : a*d*A false false=0 := by linear_combination (A false false)*ht-(A true true)*h2
    exact mul_ne_zero (mul_ne_zero harg hd) ha bad
  · simp [capped,value,funext_iff,Fin.forall_fin_succ,Equiv.swap_apply_def] at ht h1
    have bad : a*d*A false false=0 := by linear_combination (A false false)*ht-(A true true)*h1
    exact mul_ne_zero (mul_ne_zero harg hd) ha bad

theorem alternative (A B : Bool→Bool→K) (d a scalar : K)
    (ha : A false false≠0) (hb : B false false≠0) (hd : d≠0) (harg : a≠0)
    (hs : scalar≠0) (i : Fin 4) :
    Prime (⟨3,fun x=>scalar*capped (value A B d) i a x⟩ : AnySignature K) ∨
      ((fun x=>scalar*capped (value A B d) i a x)≠0 ∧
        scalar*capped (value A B d) i a (fun _=>false)=0) := by
  classical
  by_cases zero : capped (value A B d) i a (fun _=>false)=0
  · right
    refine ⟨?_,by rw [zero,mul_zero]⟩
    intro h
    apply nonzero A B d a ha hb hd harg i
    funext x
    have hx:=congrFun h x
    exact (mul_eq_zero.mp hx).resolve_left hs
  · left
    apply C.prime_of_cubic
    rw [C.scale,cubic]
    exact mul_ne_zero (pow_ne_zero 3 hs) (mul_ne_zero (mul_ne_zero harg hd) (pow_ne_zero 2 zero))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryQuaternaryCapCubic
end
