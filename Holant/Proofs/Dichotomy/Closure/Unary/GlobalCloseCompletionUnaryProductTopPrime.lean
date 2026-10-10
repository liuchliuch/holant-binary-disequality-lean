import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPinnedProduct
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroOrigin
import Mathlib.Tactic.LinearCombination

/-! The all-unary zero-cap branch has a genuine two-product normal form.
Its nonzero top correction forces primality across every original port cut.
An ordinary loop either preserves a smaller nonbinary prime or gives the
zero-origin opposite-pin source. No generic tensor-primality oracle is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopPrime
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
namespace P
export GlobalCloseCompletionUnaryPinnedProduct (canonical single cap UnaryProduct reconstruct top_difference_nonzero)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {n m k : ℕ}

def value (w : Fin n→K) (c d : K) : Signature K n :=
  fun x=>c*(∏i,if x i then w i else 1)+if x=(fun _=>true) then d else 0

def word (ports : (Fin m ⊕ Fin k) ≃ Fin n) (a b : Bool) : Fin n→Bool :=
  fun i=>Sum.elim (fun _=>a) (fun _=>b) (ports.symm i)

theorem word_false (ports : (Fin m ⊕ Fin k) ≃ Fin n) : word ports false false=(fun _=>false) := by
  funext i
  unfold word
  cases ports.symm i <;> rfl
theorem word_true (ports : (Fin m ⊕ Fin k) ≃ Fin n) : word ports true true=(fun _=>true) := by
  funext i
  unfold word
  cases ports.symm i <;> rfl
theorem word_left (ports : (Fin m ⊕ Fin k) ≃ Fin n) (a b : Bool) (i : Fin m) :
    word ports a b (ports (.inl i))=a := by simp [word]
theorem word_right (ports : (Fin m ⊕ Fin k) ≃ Fin n) (a b : Bool) (i : Fin k) :
    word ports a b (ports (.inr i))=b := by simp [word]
theorem word_not_top_left (ports : (Fin m ⊕ Fin k) ≃ Fin n) (positive : 0<m) (b : Bool) :
    word ports false b≠(fun _=>true) := by
  intro same
  have h:=congrFun same (ports (.inl ⟨0,positive⟩))
  simp [word_left] at h
theorem word_not_top_right (ports : (Fin m ⊕ Fin k) ≃ Fin n) (positive : 0<k) (a : Bool) :
    word ports a false≠(fun _=>true) := by
  intro same
  have h:=congrFun same (ports (.inr ⟨0,positive⟩))
  simp [word_right] at h

theorem product_word (ports : (Fin m ⊕ Fin k) ≃ Fin n) (w : Fin n→K) (a b : Bool) :
    (∏i,if word ports a b i then w i else 1)=
      (∏i : Fin m,if a then w (ports (.inl i)) else 1)*
      (∏i : Fin k,if b then w (ports (.inr i)) else 1) := by
  rw [←ports.prod_comp,Fintype.prod_sum_type]
  simp only [word_left,word_right]

theorem split_minor {f l r : AnySignature K} (s : ProperSplit f l r) :
    f.2 (word s.ports false false)*f.2 (word s.ports true true)=
      f.2 (word s.ports false true)*f.2 (word s.ports true false) := by
  rw [s.equation]
  simp only [word_left,word_right]
  ring

/-- Both summands survive, so each positive original partition has a
nonzero two-by-two flattening minor c*d. -/
theorem prime (w : Fin n→K) (c d : K) (positive : 0<n) (hc : c≠0) (hd : d≠0) :
    Prime (⟨n,value w c d⟩ : AnySignature K) := by
  classical
  have origin : value w c d (fun _=>false)=c := by
    have different : (fun _ : Fin n=>false)≠(fun _=>true) := by
      intro h
      have hx:=congrFun h ⟨0,positive⟩
      contradiction
    simp [value,different]
  refine ⟨?_,?_⟩
  · intro zero
    apply hc
    exact origin.symm.trans (congrFun zero (fun _=>false))
  · rintro ⟨l,r,⟨split⟩⟩
    have minor:=split_minor split
    have h00:=word_not_top_left split.ports split.left_pos false
    have h01:=word_not_top_left split.ports split.left_pos true
    have h10:=word_not_top_right split.ports split.right_pos true
    change value w c d _*value w c d _=value w c d _*value w c d _ at minor
    simp only [value,h00,h01,h10,word_true,ite_false,ite_true,add_zero] at minor
    have p00:=product_word split.ports w false false
    have p01:=product_word split.ports w false true
    have p10:=product_word split.ports w true false
    have p11:=product_word split.ports w true true
    rw [word_true] at p11
    simp only [Bool.false_eq_true,ite_false,ite_true,Finset.prod_const_one,one_mul,mul_one] at p00 p01 p10 p11
    rw [p00,p01,p10,p11] at minor
    have zero : c*d=0 := by linear_combination minor
    exact (mul_ne_zero hc hd) zero

theorem contract (w : Fin (n+2)→K) (c d : K) :
    Signature.contract Signature.equality (value w c d)=
      value (fun i=>w i.succ.succ) (c*(1+w 0*w 1)) d := by
  classical
  funext x
  rw [Signature.contract_equality]
  have h1 : (0 : Fin (n+1)).succ=(1 : Fin (n+2)) := Fin.ext rfl
  simp only [value,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,ite_false,ite_true,
    funext_iff,Fin.forall_fin_succ,Bool.false_eq_true,and_true,false_and,
    true_and,one_mul,h1]
  split_ifs <;> ring

theorem normal_form (f : Signature K n) (origin : f (fun _=>false)≠0)
    (caps : ∀i,P.UnaryProduct (P.cap i f)) :
    f=value (fun i=>f (P.single i)/f (fun _=>false)) (f (fun _=>false))
      (f (fun _=>true)-P.canonical f (fun _=>true)) := P.reconstruct f origin caps


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryProductTopPrime
end
