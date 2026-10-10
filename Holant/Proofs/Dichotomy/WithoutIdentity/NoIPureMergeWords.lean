import Holant.Support
import Mathlib.Tactic

/-! Finite signed-word surgery for native equality merging. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeWords
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false

def Legal {n : ℕ} (w : Fin n → Bool) : Prop := charge w % 4 = 0

theorem charge_cons {n : ℕ} (b : Bool) (w : Fin n → Bool) :
    charge (Fin.cons b w) = charge w + if b then 1 else -1 := by
  cases b <;> simp only [charge, weight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, if_false, if_true, Nat.cast_add, Nat.cast_zero, Nat.cast_one] <;> omega

theorem charge_append {n m : ℕ} (w : Fin n → Bool) (v : Fin m → Bool) :
    charge (Fin.addCases w v) = charge w + charge v := by
  simp only [charge, weight, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    Nat.cast_add]
  ring

theorem legal_reindex {n : ℕ} (w : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    Legal (fun i => w (e i)) ↔ Legal w := by
  have hw : weight (fun i => w (e i)) = weight w :=
    Equiv.sum_comp e (fun i => if w i then 1 else 0)
  simp only [Legal,charge,hw]

theorem legal_reduce {n : ℕ} (w : Fin n → Bool) (b : Bool)
    (h : Legal (Fin.addCases w (fun _ : Fin 3 => b))) : Legal (Fin.cons (!b) w) := by
  unfold Legal at *
  rw [charge_append] at h
  rw [charge_cons]
  cases b <;> simp [charge, weight] at h ⊢ <;> omega

section Permutations
variable {α : Type} [DecidableEq α]

def pairOrderAt (a b i j : α) : Equiv.Perm α :=
  (Equiv.swap b ((Equiv.swap a i).symm j)).trans (Equiv.swap a i)

theorem pairOrderAt_first (a b i j : α) (ab : a ≠ b) (ij : i ≠ j) :
    pairOrderAt a b i j a = i := by
  have hj : (Equiv.swap a i).symm j ≠ a := by
    intro h
    have hh := congrArg (Equiv.swap a i) h
    simp only [Equiv.apply_symm_apply, Equiv.swap_apply_left] at hh
    exact ij hh.symm
  simp only [pairOrderAt, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne ab (Ne.symm hj), Equiv.swap_apply_left]

theorem pairOrderAt_second (a b i j : α) : pairOrderAt a b i j b = j := by
  simp only [pairOrderAt, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.apply_symm_apply]

def tripleOrderAt (a b c i j k : α) : Equiv.Perm α :=
  (Equiv.swap c ((pairOrderAt a b i j).symm k)).trans (pairOrderAt a b i j)

theorem tripleOrderAt_first (a b c i j k : α)
    (ab : a ≠ b) (ac : a ≠ c) (ij : i ≠ j) (ik : i ≠ k) :
    tripleOrderAt a b c i j k a = i := by
  have hk : (pairOrderAt a b i j).symm k ≠ a := by
    intro h
    have hh := congrArg (pairOrderAt a b i j) h
    rw [Equiv.apply_symm_apply, pairOrderAt_first a b i j ab ij] at hh
    exact ik hh.symm
  simp only [tripleOrderAt, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne ac (Ne.symm hk), pairOrderAt_first a b i j ab ij]

theorem tripleOrderAt_second (a b c i j k : α) (bc : b ≠ c) (jk : j ≠ k) :
    tripleOrderAt a b c i j k b = j := by
  have hk : (pairOrderAt a b i j).symm k ≠ b := by
    intro h
    have hh := congrArg (pairOrderAt a b i j) h
    rw [Equiv.apply_symm_apply, pairOrderAt_second] at hh
    exact jk hh.symm
  simp only [tripleOrderAt, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne bc (Ne.symm hk), pairOrderAt_second]

theorem tripleOrderAt_third (a b c i j k : α) : tripleOrderAt a b c i j k c = k := by
  simp only [tripleOrderAt, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.apply_symm_apply]
end Permutations

theorem five_has_triple : ∀ w : Fin 5 → Bool,
    ∃ i j k : Fin 5, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ w i = w j ∧ w i = w k := by
  decide

theorem order {n : ℕ} (large : 2 ≤ n) (w : Fin (n+3) → Bool) :
    ∃ b : Bool, ∃ e : Equiv.Perm (Fin (n+3)), ∃ t : Fin n → Bool,
      (fun i => w (e i)) = Fin.addCases t (fun _ : Fin 3 => b) := by
  let inc : Fin 5 → Fin (n+3) := fun i => ⟨i.val, by omega⟩
  have injective : Function.Injective inc := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin (n+3) => k.val) h)
  obtain ⟨i,j,k,ij,ik,jk,hj,hk⟩ := five_has_triple (fun i => w (inc i))
  let a : Fin (n+3) := Fin.natAdd n (0 : Fin 3)
  let b : Fin (n+3) := Fin.natAdd n (1 : Fin 3)
  let c : Fin (n+3) := Fin.natAdd n (2 : Fin 3)
  have ab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b] at this; omega
  have ac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a,c] at this; omega
  have bc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
  let e := tripleOrderAt a b c (inc i) (inc j) (inc k)
  refine ⟨w (inc i),e,(fun i => w (e (Fin.castAdd 3 i))),?_⟩
  funext u
  obtain ⟨u,rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin 3 ≃ Fin (n+3)).surjective u
  cases u with
  | inl u => simp
  | inr u =>
    fin_cases u
    · simpa [e,a,b,c] using congrArg w
        (tripleOrderAt_first a b c (inc i) (inc j) (inc k) ab ac
          (injective.ne ij) (injective.ne ik))
    · simpa [e,a,b,c] using (congrArg w
        (tripleOrderAt_second a b c (inc i) (inc j) (inc k) bc (injective.ne jk))).trans hj.symm
    · simpa [e,a,b,c] using (congrArg w
        (tripleOrderAt_third a b c (inc i) (inc j) (inc k))).trans hk.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeWords
end
