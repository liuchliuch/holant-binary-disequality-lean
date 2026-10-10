import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBothPinColumn

/-! Both physical pin values eliminate the old zero-origin loop escape.
A small one-cap through a live intermediate column would force the forbidden
top column onto the same nonsingular binary line. Consequently all middle
columns vanish, and a positive-residual outside equality loop is nonsmall. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinColumnProjection
open Holant
namespace L
export GlobalCloseCompletionUnaryBinaryLoop (join loop loop_join)
end L
namespace C
export GlobalCloseCompletionUnaryBothPinColumn (factor)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {m : ℕ}

def capOne (F : Signature K (m+2)) (k : Fin m) : Signature K (m+2) :=
  fun z=>F (Function.update z k.succ.succ true)

theorem update_join (x : Fin 2→Bool) (y : Fin m→Bool) (k : Fin m) (b : Bool) :
    Function.update (L.join x y) k.succ.succ b=L.join x (Function.update y k b) := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun l=>?_) j) i <;>
    simp [L.join,Function.update,Fin.ext_iff]

theorem capOne_join (F : Signature K (m+2)) (k : Fin m)
    (x : Fin 2→Bool) (y : Fin m→Bool) :
    capOne F k (L.join x y)=F (L.join x (Function.update y k true)) := by
  unfold capOne
  rw [update_join]

theorem intermediate_zero (F : Signature K (m+2)) (g : Signature K 2)
    (g0 : g (fun _=>false)≠0)
    (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
    (columns : ∀y : Fin m→Bool,y≠(fun _=>true)→∃c : K,∀x,F (L.join x y)=g x*c)
    (top : ¬∃c : K,∀x,F (L.join x (fun _=>true))=g x*c)
    (caps : ∀k : Fin m,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (capOne F k))
    (y : Fin m→Bool) (notBottom : y≠(fun _=>false)) (notTop : y≠(fun _=>true)) :
    ∀x,F (L.join x y)=0 := by
  classical
  obtain ⟨c,column⟩ := columns y notTop
  by_cases zero : c=0
  · intro x;rw [column,zero,mul_zero]
  obtain ⟨k,hk⟩ : ∃k,y k=true := by
    by_contra! none
    apply notBottom
    funext k
    exact Bool.eq_false_of_not_eq_true (none k)
  have pivot (x : Fin 2→Bool) : capOne F k (L.join x y)=c*g x := by
    rw [capOne_join,Function.update_eq_self_iff.mpr hk.symm,column,mul_comm]
  obtain ⟨h,equation⟩ := C.factor (capOne F k) g y c zero g0 det pivot (caps k)
  apply False.elim
  apply top
  refine ⟨h (fun _=>true),?_⟩
  intro x
  have e := equation x (fun _=>true)
  rw [capOne_join,Function.update_eq_self] at e
  exact e

 theorem constant_pair (b : Bool) :
    (Fin.cons b (Fin.cons b (fun _ : Fin m=>b)) : Fin (m+2)→Bool)=(fun _=>b) := by
  funext i
  refine Fin.cases rfl (fun j=>Fin.cases rfl (fun _=>rfl) j) i

 theorem loop_not_small {t : ℕ} (positive : 0<t)
    (F : Signature K (t+4)) (g : Signature K 2)
    (g0 : g (fun _=>false)≠0)
    (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
    (c0 : K) (nonzero : c0≠0)
    (base : ∀x,F (L.join x (fun _=>false))=g x*c0)
    (top : ¬∃c : K,∀x,F (L.join x (fun _=>true))=g x*c)
    (middle : ∀y : Fin (t+2)→Bool,y≠(fun _=>false)→y≠(fun _=>true)→∀x,F (L.join x y)=0) :
    ¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2)
      (L.loop (fun x y=>F (L.join x y))) := by
  intro small
  let high : Fin (t+2)→Bool := Fin.cons true (Fin.cons true (fun _=>false))
  let low : Fin (t+2)→Bool := Fin.cons false (Fin.cons false (fun _=>true))
  have highBottom : high≠(fun _=>false) := by
    intro h
    have e := congrFun h 0
    change true=false at e
    contradiction
  have highTop : high≠(fun _=>true) := by
    intro h
    have e := congrFun h (⟨0,positive⟩ : Fin t).succ.succ
    change false=true at e
    contradiction
  have lowBottom : low≠(fun _=>false) := by
    intro h
    have e := congrFun h (⟨0,positive⟩ : Fin t).succ.succ
    change true=false at e
    contradiction
  have lowTop : low≠(fun _=>true) := by
    intro h
    have e := congrFun h 0
    change false=true at e
    contradiction
  have loopBottom (x : Fin 2→Bool) :
      L.loop (fun x y=>F (L.join x y)) (L.join x (fun _=>false))=c0*g x := by
    rw [L.loop_join,constant_pair false]
    change F (L.join x (fun _=>false))+F (L.join x high)=_
    rw [middle high highBottom highTop x,add_zero,base,mul_comm]
  have loopTop (x : Fin 2→Bool) :
      L.loop (fun x y=>F (L.join x y)) (L.join x (fun _=>true))=F (L.join x (fun _=>true)) := by
    rw [L.loop_join,constant_pair true]
    change F (L.join x low)+F (L.join x (fun _=>true))=_
    rw [middle low lowBottom lowTop x,zero_add]
  obtain ⟨h,equation⟩ := C.factor (L.loop (fun x y=>F (L.join x y))) g (fun _=>false) c0 nonzero
    g0 det loopBottom small
  apply top
  refine ⟨h (fun _=>true),?_⟩
  intro x
  rw [←loopTop]
  exact equation x (fun _=>true)

 theorem cap_loop_not_small {t : ℕ} (positive : 0<t)
    (F : Signature K (t+4)) (g : Signature K 2)
    (g0 : g (fun _=>false)≠0)
    (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
    (c0 : K) (nonzero : c0≠0)
    (base : ∀x,F (L.join x (fun _=>false))=g x*c0)
    (columns : ∀y : Fin (t+2)→Bool,y≠(fun _=>true)→∃c : K,∀x,F (L.join x y)=g x*c)
    (top : ¬∃c : K,∀x,F (L.join x (fun _=>true))=g x*c)
    (caps : ∀k : Fin (t+2),Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (capOne F k)) :
    ¬Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2)
      (L.loop (fun x y=>F (L.join x y))) :=
  loop_not_small positive F g g0 det c0 nonzero base top
    (intermediate_zero F g g0 det columns top caps)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinColumnProjection
end
