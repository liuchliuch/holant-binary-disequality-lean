import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryFactor
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFactorUniqueness
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-! Ordinary-loop propagation of the SAME nonsingular binary factor.
The pair section of the loop is read from two zero-capped source columns.
When the loop has a small factorization and a nonzero origin, its anchored
minor forces the same pair block, with the exact normalization recovered. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryLoop
open Holant
namespace B
export GlobalCloseCompletionUnaryBinaryFactor (pair outside small_factor_identity)
end B
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double)
export GlobalCloseCompletionUnaryPinnedProduct (single)
end I
namespace R
export GlobalCloseCompletionUnaryPinLoopFactor (zeroPair)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] {m : ℕ}

def join (x : Fin 2→Bool) (y : Fin m→Bool) : Fin (m+2)→Bool :=
  Fin.cons (x 0) (Fin.cons (x 1) y)
def loop (F : (Fin 2→Bool)→(Fin (m+2)→Bool)→K) : Signature K (m+2) :=
  fun z=>F ![z 0,z 1] (Fin.cons false (Fin.cons false (fun k=>z k.succ.succ)))+
    F ![z 0,z 1] (Fin.cons true (Fin.cons true (fun k=>z k.succ.succ)))

theorem pair_word (a b : Bool) :
    B.pair (0 : Fin (m+2)) 1 a b=Fin.cons a (Fin.cons b (fun _=>false)) := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i
  · simp [B.pair,Function.update,Fin.ext_iff]
  · simp [B.pair,Function.update,Fin.ext_iff]
  · simp [B.pair,Function.update,Fin.ext_iff]

theorem pair_bottom : B.pair (0 : Fin (m+2)) 1 false false=(fun _=>false) := by
  rw [pair_word]
  funext i
  refine Fin.cases rfl (fun j=>Fin.cases rfl (fun _=>rfl) j) i

theorem single0 : I.single (0 : Fin (m+2))=B.pair 0 1 true false := by
  rw [pair_word]
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i <;>
    simp [I.single,Function.update,Fin.ext_iff]
theorem single1 : I.single (1 : Fin (m+2))=B.pair 0 1 false true := by
  rw [pair_word]
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i <;>
    simp [I.single,Function.update,Fin.ext_iff]

theorem section_minor (G : Signature K (m+2)) (g : Signature K 2) (c : K)
    (sections : ∀a b,G (B.pair 0 1 a b)=g ![a,b]*c) :
    I.minor G 0 1=
      (g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false])*c^2 := by
  unfold I.minor
  rw [←pair_bottom,single0,single1]
  change G (B.pair 0 1 false false)*G (B.pair 0 1 true true)-
    G (B.pair 0 1 true false)*G (B.pair 0 1 false true)=_
  rw [sections,sections,sections,sections]
  ring

theorem loop_join (F : (Fin 2→Bool)→(Fin (m+2)→Bool)→K)
    (x : Fin 2→Bool) (y : Fin m→Bool) :
    loop F (join x y)=F x (Fin.cons false (Fin.cons false y))+
      F x (Fin.cons true (Fin.cons true y)) := by
  have hx : ![x 0,x 1]=x := by funext i;fin_cases i <;>rfl
  simp [loop,join,hx]

theorem zeroPair_word : R.zeroPair (n:=m)=Fin.cons false (Fin.cons false (fun _=>true)) := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i <;>
    simp [R.zeroPair,Fin.val_succ]

theorem outside_join (x : Fin 2→Bool) (y : Fin m→Bool) :
    B.outside 0 1 (join x y)=join (fun _=>false) y := by
  funext i
  refine Fin.cases ?_ (fun j=>Fin.cases ?_ (fun k=>?_) j) i <;>
    simp [B.outside,join,Function.update,Fin.ext_iff]

variable (F : (Fin 2→Bool)→(Fin (m+2)→Bool)→K) (g : Signature K 2)
variable (positive : 0<m) (g0 : g (fun _=>false)≠0)
variable (det : g ![false,false]*g ![true,true]-g ![false,true]*g ![true,false]≠0)
variable (caps : ∀y,y≠(fun _=>true)→∃c : K,∀x,F x y=g x*c)
variable (small : Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (loop F))

include positive g0 det caps small in
theorem propagate (regular : loop F=0 ∨ loop F (fun _=>false)≠0) :
    ∃c : K,∀x,F x R.zeroPair+F x (fun _=>true)=g x*c := by
  classical
  have top : (Fin.cons true (Fin.cons true (fun _ : Fin m=>true)) : Fin (m+2)→Bool)=(fun _=>true) := by
    funext i
    refine Fin.cases rfl (fun j=>Fin.cases rfl (fun _=>rfl) j) i
  have bottom : (![false,false] : Fin 2→Bool)=(fun _=>false) := by
    funext i
    fin_cases i <;>rfl
  rcases regular with zero|origin
  · refine ⟨0,?_⟩
    intro x
    have h:=congrFun zero (join x (fun _=>true))
    rw [loop_join,←zeroPair_word,top] at h
    simpa using h
  · have h00 : (Fin.cons false (Fin.cons false (fun _ : Fin m=>false)) : Fin (m+2)→Bool)≠(fun _=>true) := by
      intro h
      have hh:=congrFun h 0
      simp at hh
    have h11 : (Fin.cons true (Fin.cons true (fun _ : Fin m=>false)) : Fin (m+2)→Bool)≠(fun _=>true) := by
      intro h
      have hh:=congrFun h (⟨0,positive⟩ : Fin m).succ.succ
      change false=true at hh
      contradiction
    obtain ⟨a,ha⟩:=caps _ h00
    obtain ⟨b,hb⟩:=caps _ h11
    have sections (p q : Bool) : loop F (B.pair 0 1 p q)=g ![p,q]*(a+b) := by
      rw [pair_word]
      change loop F (join ![p,q] (fun _=>false))=_
      rw [loop_join,ha,hb,mul_add]
    have zeroSection : loop F (fun _=>false)=g (fun _=>false)*(a+b) := by
      have h:=sections false false
      rw [pair_bottom] at h
      simpa only [bottom] using h
    have sumNonzero : a+b≠0 := by
      intro h
      apply origin
      rw [zeroSection,h,mul_zero]
    have edge : I.minor (loop F) 0 1≠0 := by
      rw [section_minor (loop F) g (a+b) sections]
      exact mul_ne_zero det (pow_ne_zero 2 sumNonzero)
    let h:=loop F (join (fun _=>false) (fun _=>true))
    refine ⟨h/g (fun _=>false),?_⟩
    intro x
    have different : (0 : Fin (m+2))≠1 := by
      intro equal
      have h:=congrArg Fin.val equal
      have hm : 1<m+2 := by omega
      simpa [Nat.mod_eq_of_lt hm] using h
    have fact:=B.small_factor_identity (loop F) small (0 : Fin (m+2)) 1 different edge (join x (fun _=>true))
    rw [zeroSection,outside_join] at fact
    change loop F (join x (fun _=>true))*(g (fun _=>false)*(a+b))=
      loop F (B.pair 0 1 (x 0) (x 1))*h at fact
    rw [sections] at fact
    have hx : ![x 0,x 1]=x := by funext i;fin_cases i <;>rfl
    rw [hx] at fact
    have uncancelled : (loop F (join x (fun _=>true))*g (fun _=>false))*(a+b)=
        (g x*h)*(a+b) := by linear_combination fact
    have cancel:=mul_right_cancel₀ sumNonzero uncancelled
    have value : loop F (join x (fun _=>true))=g x*(h/g (fun _=>false)) := by
      rw [←mul_div_assoc]
      exact (eq_div_iff g0).mpr cancel
    rw [loop_join,←zeroPair_word,top] at value
    exact value

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryLoop
end
