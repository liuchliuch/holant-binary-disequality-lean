import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFactorUniqueness
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Canonical reconstruction for the all-unary zero-cap branch of UPF.
Every zero-pinned product agrees with one product fixed by the original
zero and singleton coefficients. Thus the original row differs from that
product at only the all-one word. No positivity or conjugate norm is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPinnedProduct
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def UnaryProduct (f : Signature K n) : Prop :=
  ∃c : K,∃w : Fin n→Bool→K,∀x,f x=c*∏i,w i (x i)
def single (i : Fin n) : Fin n→Bool := Function.update (fun _=>false) i true
def canonical (f : Signature K n) : Signature K n :=
  fun x=>f (fun _=>false)*∏i,if x i then f (single i)/f (fun _=>false) else 1
def cap (i : Fin n) (f : Signature K n) : Signature K n :=
  fun x=>f (Function.update x i false)

theorem unary_normalized (f : Signature K n) (product : UnaryProduct f)
    (origin : f (fun _=>false)≠0) : f=canonical f := by
  classical
  obtain ⟨c,w,equation⟩ := product
  have w0 : ∀i,w i false≠0 := by
    have h := origin
    rw [equation] at h
    exact fun i=>(Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2) i (Finset.mem_univ i)
  have ratio (x : Fin n→Bool) : f x=f (fun _=>false)*∏i,w i (x i)/w i false := by
    rw [equation x,equation (fun _=>false),mul_assoc,←Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    field_simp [w0 i]
  have singleton (i : Fin n) : f (single i)=f (fun _=>false)*(w i true/w i false) := by
    rw [ratio]
    congr 1
    have hp : (∏j,w j (single i j)/w j false)=w i (single i i)/w i false := by
      apply Finset.prod_eq_single i
      · intro j _ hji
        simp [single,Function.update_of_ne hji,w0 j]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))
    simpa [single] using hp
  funext x
  rw [ratio]
  unfold canonical
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases hx : x i with
  | false=>simp [hx,w0 i]
  | true=>simp [hx,singleton i,origin]

@[simp] theorem cap_origin (f : Signature K n) (i : Fin n) :
    cap i f (fun _=>false)=f (fun _=>false) := by
  unfold cap
  congr 1
  funext j
  by_cases hji : j=i <;> simp [hji]

theorem cap_single (f : Signature K n) (i j : Fin n) (different : j≠i) :
    cap i f (single j)=f (single j) := by
  unfold cap
  congr 1
  funext k
  by_cases hki : k=i
  · subst k
    simp [single,Ne.symm different]
  · simp [hki]

theorem cap_canonical (f : Signature K n) (i : Fin n) (x : Fin n→Bool)
    (zero : x i=false) : canonical (cap i f) x=canonical f x := by
  classical
  unfold canonical
  rw [cap_origin]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hji : j=i
  · subst j
    simp [zero]
  · rw [cap_single f i j hji]

theorem off_top (f : Signature K n) (origin : f (fun _=>false)≠0)
    (caps : ∀i,UnaryProduct (cap i f)) (x : Fin n→Bool) (off : x≠(fun _=>true)) :
    f x=canonical f x := by
  classical
  obtain ⟨i,hi⟩ : ∃i,x i=false := by
    by_contra none
    push Not at none
    exact off (funext fun i=>Bool.eq_true_of_not_eq_false (none i))
  have pinned : cap i f x=f x := by
    unfold cap
    congr 1
    funext j
    by_cases hji : j=i <;> simp [hji,hi]
  rw [←pinned,unary_normalized (cap i f) (caps i) (by simpa using origin)]
  exact cap_canonical f i x hi

/-- The only undetermined coefficient is recorded explicitly. -/
theorem reconstruct (f : Signature K n) (origin : f (fun _=>false)≠0)
    (caps : ∀i,UnaryProduct (cap i f)) :
    f=fun x=>canonical f x+
      if x=(fun _=>true) then f (fun _=>true)-canonical f (fun _=>true) else 0 := by
  classical
  funext x
  by_cases hx : x=(fun _=>true)
  · subst x
    simp
  · simp [hx,off_top f origin caps x hx]

/-- A coordinatewise product is a genuine proper split on any two positive
port blocks; this supplies the exact primality contradiction used later. -/
theorem product_split {m k : ℕ} (ports : (Fin m ⊕ Fin k) ≃ Fin n)
    (left : 0<m) (right : 0<k) (f : Signature K n) (product : UnaryProduct f) :
    ∃a b : AnySignature K,Nonempty (ProperSplit (⟨n,f⟩ : AnySignature K) a b) := by
  obtain ⟨c,w,equation⟩ := product
  refine ⟨⟨m,fun x=>c*∏i,w (ports (.inl i)) (x i)⟩,
    ⟨k,fun x=>∏i,w (ports (.inr i)) (x i)⟩,
    ⟨{left_pos:=left,right_pos:=right,ports:=ports,scale:=1,equation:=?_}⟩⟩
  funext x
  dsimp only
  rw [equation,←ports.prod_comp (fun i=>w i (x i)),Fintype.prod_sum_type]
  simp only [Units.val_one,one_mul]
  ring

theorem prime_not_unaryProduct (f : Signature K n) (large : 2≤n)
    (prime : Prime (⟨n,f⟩ : AnySignature K)) : ¬UnaryProduct f := by
  intro product
  let ports : (Fin 1 ⊕ Fin (n-1)) ≃ Fin n :=
    (finSumFinEquiv : (Fin 1 ⊕ Fin (n-1)) ≃ Fin (1+(n-1))).trans (finCongr (by omega))
  exact prime.2 (product_split ports (by omega) (by omega) f product)

theorem canonical_product (f : Signature K n) : UnaryProduct (canonical f) :=
  ⟨f (fun _=>false),fun i b=>if b then f (single i)/f (fun _=>false) else 1,fun _=>rfl⟩

/-- At a genuine prime the missing top coefficient cannot equal the
coordinatewise product. It is a nonzero second tensor summand. -/
theorem top_difference_nonzero (f : Signature K n) (large : 2≤n)
    (prime : Prime (⟨n,f⟩ : AnySignature K)) (origin : f (fun _=>false)≠0)
    (caps : ∀i,UnaryProduct (cap i f)) :
    f (fun _=>true)-canonical f (fun _=>true)≠0 := by
  intro zero
  apply prime_not_unaryProduct f large prime
  have equation := reconstruct f origin caps
  have exactF : f=canonical f := by
    rw [zero] at equation
    simpa only [ite_self,add_zero] using equation
  rw [exactF]
  exact canonical_product f


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPinnedProduct
end
