import Holant.Dihedral.CompatibleCoefficientLine.Source

/-! Coefficient-free port permutations for an aligned source matching. -/
noncomputable section
namespace Holant.Dihedral.CompatibleCoefficientLine
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure

def boolIndex : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i=1
  left_inv b := by cases b <;> decide
  right_inv i := by fin_cases i <;> decide

def pairPorts (r : ℕ) : (Fin (r+1) × Bool) ≃ Fin (2*r+2) :=
  (Equiv.prodCongr (Equiv.refl _) boolIndex).trans
    (finProdFinEquiv.trans (finCongr (by omega)))

theorem pairPorts_val (r : ℕ) (e : Fin (r+1)) (b : Bool) :
    (pairPorts r (e,b)).val = 2*e.val+(if b then 1 else 0) := by
  cases b <;> simp [pairPorts,boolIndex,finProdFinEquiv,Nat.add_comm]

theorem pairPorts_succ (r : ℕ) (e : Fin (r+1)) (b : Bool) :
    pairPorts (r+1) (e.succ,b) = (pairPorts r (e,b)).succ.succ := by
  apply Fin.ext
  simp only [pairPorts_val,Fin.val_succ]
  omega

theorem pairPorts_zero_false (r : ℕ) : pairPorts r (0,false)=0 := by
  apply Fin.ext; simp [pairPorts_val]
theorem pairPorts_zero_true (r : ℕ) : pairPorts r (0,true)=1 := by
  apply Fin.ext; simp [pairPorts_val]

/-- The recursive product is the complete literal original coefficient product. -/
theorem product_eq_full (r : ℕ) (A : Fin (r+1) → Mat) (x : Fin (2*r+2) → Bool) :
    product r (fun e => A e.castSucc) (A (Fin.last r)) x =
      ∏ e, A e (x (pairPorts r (e,false))) (x (pairPorts r (e,true))) := by
  induction r with
  | zero => simp [product,pairPorts_zero_false,pairPorts_zero_true]
  | succ r ih =>
    rw [Fin.prod_univ_succ]
    simp only [product,pairPorts_zero_false,pairPorts_zero_true]
    change A 0 (x 0) (x 1) *
      product r (fun i => A i.castSucc.succ) (A (Fin.last r).succ) (tail x) = _
    rw [ih (fun i => A i.succ) (tail x)]
    congr 1

def liftOne {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun i := Fin.cases 0 (fun j => (p j).succ) i
  invFun i := Fin.cases 0 (fun j => (p.symm j).succ) i
  left_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp

def liftPair {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+2)) := liftOne (liftOne p)

theorem word_liftPair {n : ℕ} (p : Equiv.Perm (Fin n)) (a b : Bool) (x : Fin n → Bool) :
    (fun i => pair a b x ((liftPair p).symm i)) = pair a b (fun i => x (p.symm i)) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl

def swapFunction (n : ℕ) : Fin (n+4) → Fin (n+4) :=
  Fin.cons ((0 : Fin (n+2)).succ.succ)
    (Fin.cons ((0 : Fin (n+1)).succ.succ.succ)
      (Fin.cons 0 (Fin.cons ((0 : Fin (n+3)).succ) (fun i => i.succ.succ.succ.succ))))

theorem swapFunction_involutive (n : ℕ) : Function.Involutive (swapFunction n) := by
  intro i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i) i
  all_goals rfl

def swapPairs (n : ℕ) : Equiv.Perm (Fin (n+4)) where
  toFun := swapFunction n
  invFun := swapFunction n
  left_inv := swapFunction_involutive n
  right_inv := swapFunction_involutive n

theorem word_swapPairs {n : ℕ} (a b c d : Bool) (x : Fin n → Bool) :
    (fun i => pair a b (pair c d x) ((swapPairs n).symm i)) = pair c d (pair a b x) := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i) i) i
  all_goals rfl

def shuffleDeleted : (r : ℕ) → Equiv.Perm (Fin (2*r+4))
  | 0 => Equiv.refl _
  | r+1 => (liftPair (shuffleDeleted r)).trans (swapPairs (2*r+2))

/-- Exact word-level transport, independent of every signature coefficient. -/
theorem word_shuffleDeleted (r : ℕ) (a b : Bool) (x : Fin (2*r+2) → Bool) :
    (fun i => insertDeleted r a b x ((shuffleDeleted r).symm i)) = pair a b x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    have h : (fun i => insertDeleted (r+1) a b x ((liftPair (shuffleDeleted r)).symm i)) =
        pair (x 0) (x 1) (pair a b (tail x)) := by
      change (fun i => pair (x 0) (x 1) (insertDeleted r a b (tail x))
        ((liftPair (shuffleDeleted r)).symm i)) = _
      rw [word_liftPair,ih]
      rfl
    have hh := congrArg (fun w : Fin (2*r+6) → Bool => fun i => w ((swapPairs (2*r+2)).symm i)) h
    change (fun i => insertDeleted (r+1) a b x ((shuffleDeleted (r+1)).symm i)) = _ at hh
    rw [word_swapPairs,pair_eta] at hh
    exact hh

theorem shuffleDeleted_p0 (r : ℕ) : shuffleDeleted r ⟨2*r,by omega⟩ = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change swapFunction (2*r+2) ((shuffleDeleted r ⟨2*r,by omega⟩).succ.succ) = 0
    rw [ih]
    rfl

theorem shuffleDeleted_p1 (r : ℕ) : shuffleDeleted r ⟨2*r+1,by omega⟩ = 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change swapFunction (2*r+2) ((shuffleDeleted r ⟨2*r+1,by omega⟩).succ.succ) = 1
    rw [ih]
    rfl

theorem shuffleDeleted_e0 (r : ℕ) : shuffleDeleted r ⟨2*r+2,by omega⟩ = ⟨2*r+2,by omega⟩ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change swapFunction (2*r+2) ((shuffleDeleted r ⟨2*r+2,by omega⟩).succ.succ) = _
    rw [ih]
    rfl

theorem shuffleDeleted_e1 (r : ℕ) : shuffleDeleted r ⟨2*r+3,by omega⟩ = ⟨2*r+3,by omega⟩ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change swapFunction (2*r+2) ((shuffleDeleted r ⟨2*r+3,by omega⟩).succ.succ) = _
    rw [ih]
    rfl

/-- Move a source residual matching into the closure order while retaining p. -/
def ancestorOrder (r : ℕ) (p : Equiv.Perm (Fin (2*r+2))) : Equiv.Perm (Fin (2*r+4)) :=
  (shuffleDeleted r).trans (liftPair p)

theorem ordered_card (r : ℕ) (p : Equiv.Perm (Fin (2*r+2)))
    (f : Signature Scalar (2*r+4)) (K : Mat) :
    card r (Tensor.reindex (ancestorOrder r p).symm f) K =
      Tensor.reindex p.symm (Signature.contract K f) := by
  funext x
  have hi (a b : Bool) :
      (fun i => insertDeleted r a b x ((ancestorOrder r p).symm i)) =
        pair a b (fun i => x (p.symm i)) := by
    have h := congrArg (fun w : Fin (2*r+4) → Bool => fun i => w ((liftPair p).symm i))
      (word_shuffleDeleted r a b x)
    change (fun i => insertDeleted r a b x ((ancestorOrder r p).symm i)) = _ at h
    rw [word_liftPair] at h
    exact h
  simp only [card,Tensor.reindex,Signature.contract,hi]

theorem ordered_physicalCard (r : ℕ) (p : Equiv.Perm (Fin (2*r+2)))
    (f : Signature Scalar (2*r+4)) (C : Mat) :
    physicalCard r (Tensor.reindex (ancestorOrder r p).symm f) C =
      Tensor.reindex p.symm (nativeCardValue f C) :=
  ordered_card r p f (fun a b => C (!a) (!b))

end Holant.Dihedral.CompatibleCoefficientLine
