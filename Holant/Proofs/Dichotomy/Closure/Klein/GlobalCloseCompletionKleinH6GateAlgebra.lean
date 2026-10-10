import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateData
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMOriginal
import Holant.Tractable.AffineOperations

/-! The H6 transform has its actual transpose as an inverse up to four.
Both directions preserve the native algebraic affine class. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateAlgebra
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
namespace D
export GlobalCloseCompletionKleinH6GateData (Word3 join matrix inverse matrix_cast)
end D
namespace H
export GlobalCloseCompletionKleinH6RMBell (core core_algebraic)
end H
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

def front (x : Fin (n+3)→Bool) : D.Word3 := ![x 0,Fin.tail x 0,Fin.tail (Fin.tail x) 0]
def tail (x : Fin (n+3)→Bool) : Fin n→Bool := Fin.tail (Fin.tail (Fin.tail x))
def append (u : D.Word3) (z : Fin n→Bool) : Fin (n+3)→Bool := Fin.cons (u 0) (Fin.cons (u 1) (Fin.cons (u 2) z))

theorem front_append (u : D.Word3) (z : Fin n→Bool) : front (append u z)=u := by funext i;fin_cases i <;> rfl
theorem tail_append (u : D.Word3) (z : Fin n→Bool) : tail (append u z)=z := rfl
theorem append_front_tail (x : Fin (n+3)→Bool) : append (front x) (tail x)=x := by
  change Fin.cons (x 0) (Fin.cons (Fin.tail x 0)
    (Fin.cons (Fin.tail (Fin.tail x) 0) (Fin.tail (Fin.tail (Fin.tail x)))))=x
  simp only [Fin.cons_self_tail]


theorem sum_cons {m : ℕ} (f : (Fin (m+1)→Bool)→K) :
    (∑x,f x)=∑b : Bool,∑x : Fin m→Bool,f (Fin.cons b x) := by
  let : Fintype (Bool×(Fin m→Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
  rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Bool)).sum_comp,Fintype.sum_prod_type]
  rfl

theorem sum_three (f : D.Word3→K) :
    (∑x,f x)=∑a : Bool,∑b : Bool,∑c : Bool,f ![a,b,c] := by
  rw [sum_cons]
  simp_rw [sum_cons]
  simp only [Fintype.sum_unique]
  rfl

def action (b : Bool) (f : Signature K (n+3)) : Signature K (n+3) :=
  fun x=>∑u : D.Word3,(D.matrix b (front x) u:K)*f (append u (tail x))

theorem action_scale (b : Bool) (f : Signature K (n+3)) (c : K) : action b (c • f)=c • action b f := by
  funext x
  simp only [action,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem map_action (phi : K→+*L) (b : Bool) (f : Signature K (n+3)) :
    RH.mapSignature phi (action b f)=action b (RH.mapSignature phi f) := by
  funext x
  simp only [RH.mapSignature,action,map_sum,map_mul,map_intCast]

theorem inverse (b : Bool) (f : Signature K (n+3)) : action (!b) (action b f)=(4:K) • f := by
  funext x
  simp only [action,front_append,tail_append,Finset.mul_sum]
  rw [Finset.sum_comm]
  have inner (y : D.Word3) :
      (∑u : D.Word3,(D.matrix (!b) (front x) u:K)*((D.matrix b u y:K)*f (append y (tail x))))=
        (if front x=y then (4:K) else 0)*f (append y (tail x)) := by
    have gram := congrArg (fun z : ℤ=>(z:K)) (D.inverse b (front x) y)
    simp only [Int.cast_sum,Int.cast_mul,Int.cast_ite,Int.cast_ofNat,Int.cast_zero] at gram
    calc
      _=(∑u : D.Word3,(D.matrix (!b) (front x) u:K)*(D.matrix b u y:K))*f (append y (tail x)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u _
        ring
      _=_ := by rw [gram]
  simp_rw [inner]
  simp only [ite_mul,zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ,ite_true,append_front_tail,Pi.smul_apply,smul_eq_mul]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateAlgebra
end
