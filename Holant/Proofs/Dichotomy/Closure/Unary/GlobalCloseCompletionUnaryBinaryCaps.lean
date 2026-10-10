import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryBinaryFactor
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPinLoopFactor
import Mathlib.Tactic.FinCases

/-! The binary factor for the UPF step is selected from actual anchored
coefficients, then propagated to every outside zero column. No caller gives
the factor or its cap equations: both are derived from the small cap trees. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryCaps
open Holant
namespace B
export GlobalCloseCompletionUnaryBinaryFactor (pair outside common_cap_factor)
end B
namespace I
export GlobalCloseCompletionUnaryProductInteraction (minor double)
export GlobalCloseCompletionUnaryPinnedProduct (single cap)
end I
namespace R
export GlobalCloseCompletionUnaryPinLoopFactor (block)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] {m k : ℕ}
variable (ports : (Fin 2 ⊕ Fin (m+2)) ≃ Fin k) (f : Signature K k)

def first : Fin k := ports (.inl 0)
def second : Fin k := ports (.inl 1)
theorem distinct : first ports≠second ports := by
  intro h
  have hh:=ports.injective h
  have hv:=Sum.inl.inj hh
  have hn:=congrArg Fin.val hv
  contradiction

def word (x : Fin 2→Bool) (y : Fin (m+2)→Bool) : Fin k→Bool :=
  fun i=>Sum.elim x y (ports.symm i)
def factor : Signature K 2 :=
  fun x=>f (B.pair (first ports) (second ports) (x 0) (x 1))/f (fun _=>false)

theorem pair_bottom (i j : Fin k) : B.pair i j false false=(fun _=>false) := by
  funext l
  by_cases hi : l=i <;> by_cases hj : l=j <;> simp [B.pair,Function.update,hi,hj]
theorem pair_single_first (i j : Fin k) (different : i≠j) : B.pair i j true false=I.single i := by
  funext l
  by_cases hi : l=i
  · subst l
    simp [B.pair,I.single,Function.update,different]
  · by_cases hj : l=j
    · subst l
      simp [B.pair,I.single,Function.update,hi]
    · simp [B.pair,I.single,Function.update,hi,hj]
theorem pair_single_second (i j : Fin k) : B.pair i j false true=I.single j := by
  funext l
  by_cases hi : l=i <;> by_cases hj : l=j <;> simp [B.pair,I.single,Function.update,hi,hj]

theorem factor_origin (origin : f (fun _=>false)≠0) : factor ports f (fun _=>false)=1 := by
  simp [factor,pair_bottom,origin]

theorem factor_det (origin : f (fun _=>false)≠0) :
    factor ports f ![false,false]*factor ports f ![true,true]-
      factor ports f ![false,true]*factor ports f ![true,false]=
        I.minor f (first ports) (second ports)/(f (fun _=>false))^2 := by
  simp only [factor,Matrix.cons_val_zero,Matrix.cons_val_one,pair_bottom,
    pair_single_first _ _ (distinct ports),pair_single_second]
  unfold I.minor I.double I.single
  change _=((f (fun _=>false)*f (B.pair (first ports) (second ports) true true))-
    f (Function.update (fun _=>false) (first ports) true)*
      f (Function.update (fun _=>false) (second ports) true))/(f (fun _=>false))^2
  field_simp [origin]

theorem outside_word (x : Fin 2→Bool) (y : Fin (m+2)→Bool) :
    B.outside (first ports) (second ports) (word ports x y)=word ports (fun _=>false) y := by
  funext z
  obtain ⟨p,rfl⟩:=ports.surjective z
  cases p with
  | inl j=>
    fin_cases j <;> simp [B.outside,word,first,second,Function.update,Equiv.apply_eq_iff_eq]
  | inr j=>simp [B.outside,word,first,second,Function.update,Equiv.apply_eq_iff_eq]

variable (origin : f (fun _=>false)≠0)
variable (edge : I.minor f (first ports) (second ports)≠0)
variable (caps : ∀i,Signature.TensorClosure (fun n (_ : Signature K n)=>n≤2) (I.cap i f))

include origin edge caps in
theorem columns : ∀y,y≠(fun _=>true)→∃c : K,∀x,R.block ports f x y=factor ports f x*c := by
  classical
  intro y off
  obtain ⟨t,ht⟩ : ∃t,y t=false := by
    by_contra none
    push Not at none
    exact off (funext fun t=>Bool.eq_true_of_not_eq_false (none t))
  let p : Fin k:=ports (.inr t)
  have ip : first ports≠p := by simp [first,p]
  have jp : second ports≠p := by simp [second,p]
  refine ⟨f (word ports (fun _=>false) y),?_⟩
  intro x
  have h:=B.common_cap_factor f caps (first ports) (second ports) p (distinct ports) ip jp edge (word ports x y)
  have capped (z : Fin 2→Bool) : I.cap p f (word ports z y)=f (word ports z y) := by
    unfold I.cap
    congr 1
    have hp : word ports z y p=false := by simp [word,p,ht]
    exact Function.update_eq_self_iff.mpr hp.symm
  rw [outside_word,capped,capped] at h
  have hx0 : word ports x y (first ports)=x 0 := by simp [word,first]
  have hx1 : word ports x y (second ports)=x 1 := by simp [word,second]
  rw [hx0,hx1] at h
  change f (word ports x y)=_
  unfold factor
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff origin).mpr h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinaryCaps
end
