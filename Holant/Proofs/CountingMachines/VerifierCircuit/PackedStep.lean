import Holant.Proofs.CountingMachines.VerifierCircuit.BoundedTableau

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.σFin

/-!
# Bounded packed execution of each actual TM2 statement

Ported reference proof. See the task validation reports.

This is a fixed-width implementation of the original heterogeneous stacks.
`aux_correct` derives its semantics from `TM2.stepAux`, including intermediate
pushes before a pop. There is no assumed simulator correctness. The extra cell
ensures an actual head coordinate even on zero-witness, empty-input instances.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.PackedStep
open Holant.LocalDrafts.CountingHardness


open Turing
open VerifierRun
open scoped BigOperators

variable (tm : FinTM2) (C : ℕ)
abbrev Packed := BoundedTableau.Packed tm (C + 1)

def packRaw (c : tm.Cfg) : Packed tm C :=
  (c.l, c.var, fun k => BoundedTableau.pad (C + 1) (c.stk k))

def state (p : Packed tm C) (v : tm.σ) : Packed tm C := (p.1, v, p.2.2)
def label (p : Packed tm C) (l : Option tm.Λ) : Packed tm C := (l, p.2)
def head (p : Packed tm C) (k : tm.K) : Option (tm.Γ k) := p.2.2 k 0

def shiftPush {A : Type} (a : A) (cells : Fin (C + 1) → Option A) :
    Fin (C + 1) → Option A :=
  fun i => if h : i.val = 0 then some a else cells ⟨i.val - 1, by omega⟩

def shiftPop {A : Type} (cells : Fin (C + 1) → Option A) : Fin (C + 1) → Option A :=
  fun i => if h : i.val + 1 < C + 1 then cells ⟨i.val + 1, h⟩ else none

def push (p : Packed tm C) (k : tm.K) (a : tm.Γ k) : Packed tm C :=
  (p.1, p.2.1, Function.update p.2.2 k (shiftPush C a (p.2.2 k)))

def pop (p : Packed tm C) (k : tm.K) : Packed tm C :=
  (p.1, p.2.1, Function.update p.2.2 k (shiftPop C (p.2.2 k)))

theorem shiftPush_pad {A : Type} (a : A) (xs : List A) :
    shiftPush C a (BoundedTableau.pad (C + 1) xs) = BoundedTableau.pad (C + 1) (a :: xs) := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero => rfl
  | succ i => simp [shiftPush, BoundedTableau.pad]

theorem shiftPop_pad {A : Type} (xs : List A) (hx : xs.length ≤ C + 1) :
    shiftPop C (BoundedTableau.pad (C + 1) xs) = BoundedTableau.pad (C + 1) xs.tail := by
  funext i
  by_cases hi : i.val + 1 < C + 1
  · simp [shiftPop, hi, BoundedTableau.pad, List.getElem?_tail]
  · have hout : xs.length ≤ i.val + 1 := by omega
    simp [shiftPop, hi, BoundedTableau.pad, List.getElem?_tail,
      List.getElem?_eq_none_iff.mpr hout]

@[simp] theorem head_packRaw (c : tm.Cfg) (k : tm.K) :
    head tm C (packRaw tm C c) k = (c.stk k).head? := by
  change (c.stk k)[0]? = (c.stk k).head?
  cases c.stk k <;> rfl

theorem push_packRaw (c : tm.Cfg) (k : tm.K) (a : tm.Γ k) :
    push tm C (packRaw tm C c) k a =
      packRaw tm C ⟨c.l, c.var, Function.update c.stk k (a :: c.stk k)⟩ := by
  change (c.l, c.var, Function.update
      (fun j => BoundedTableau.pad (C + 1) (c.stk j)) k
      (shiftPush C a (BoundedTableau.pad (C + 1) (c.stk k)))) =
    (c.l, c.var, fun j => BoundedTableau.pad (C + 1)
      (Function.update c.stk k (a :: c.stk k) j))
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext j
  by_cases hj : j = k
  · subst j
    simpa [push, packRaw] using shiftPush_pad C a (c.stk k)
  · simp [push, packRaw, hj]

theorem pop_packRaw (c : tm.Cfg) (k : tm.K) (hx : (c.stk k).length ≤ C + 1) :
    pop tm C (packRaw tm C c) k =
      packRaw tm C ⟨c.l, c.var, Function.update c.stk k (c.stk k).tail⟩ := by
  change (c.l, c.var, Function.update
      (fun j => BoundedTableau.pad (C + 1) (c.stk j)) k
      (shiftPop C (BoundedTableau.pad (C + 1) (c.stk k)))) =
    (c.l, c.var, fun j => BoundedTableau.pad (C + 1)
      (Function.update c.stk k (c.stk k).tail j))
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext j
  by_cases hj : j = k
  · subst j
    simpa [pop, packRaw] using shiftPop_pad C (c.stk k) hx
  · simp [pop, packRaw, hj]

def aux : TM2.Stmt tm.Γ tm.Λ tm.σ → Packed tm C → Packed tm C
  | .push k f q, p => aux q (push tm C p k (f p.2.1))
  | .pop k f q, p => aux q (pop tm C (state tm C p (f p.2.1 (head tm C p k))) k)
  | .peek k f q, p => aux q (state tm C p (f p.2.1 (head tm C p k)))
  | .load f q, p => aux q (state tm C p (f p.2.1))
  | .branch f q r, p => if f p.2.1 then aux q p else aux r p
  | .goto f, p => label tm C p (some (f p.2.1))
  | .halt, p => label tm C p none

/-- The capacity obligation is a concrete length-plus-syntactic-push inequality.
In particular it is not a conclusion-shaped simulation premise. -/
theorem aux_correct (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (c : tm.Cfg)
    (hc : ∀ k, (c.stk k).length + pushes q ≤ C + 1) :
    aux tm C q (packRaw tm C c) = packRaw tm C (TM2.stepAux q c.var c.stk) := by
  induction q generalizing c with
  | push k f q ih =>
    rw [aux, push_packRaw]
    apply ih
    intro j
    by_cases hj : j = k
    · subst j
      simpa [pushes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc k
    · have h := hc j
      simp only [pushes] at h
      simp only [Function.update_of_ne hj]
      omega
  | pop k f q ih =>
    rcases c with ⟨l,v,S⟩
    let intermediate : tm.Cfg := ⟨l,f v (S k).head?,S⟩
    have hlength : (intermediate.stk k).length ≤ C + 1 := by
      change (S k).length ≤ C + 1
      have h := hc k
      change (S k).length + pushes q ≤ C + 1 at h
      omega
    have hstate :
        state tm C (packRaw tm C (⟨l,v,S⟩ : tm.Cfg))
          (f (packRaw tm C (⟨l,v,S⟩ : tm.Cfg)).2.1
            (head tm C (packRaw tm C (⟨l,v,S⟩ : tm.Cfg)) k)) =
        packRaw tm C intermediate := by
      rw [head_packRaw tm C (⟨l,v,S⟩ : tm.Cfg) k]
      rfl
    simp only [aux]
    rw [hstate]
    change aux tm C q (pop tm C (packRaw tm C intermediate) k) =
      packRaw tm C (TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail))
    rw [pop_packRaw tm C intermediate k hlength]
    change aux tm C q (packRaw tm C
      (⟨l,f v (S k).head?,Function.update S k (S k).tail⟩ : tm.Cfg)) =
        packRaw tm C (TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail))
    apply ih
    intro j
    change (Function.update S k (S k).tail j).length + pushes q ≤ C + 1
    by_cases hj : j = k
    · subst j
      have h := hc k
      simp only [pushes] at h
      simp only [Function.update_self, List.length_tail]
      omega
    · simpa [hj, pushes] using hc j
  | peek k f q ih =>
    simp only [aux, head_packRaw]
    exact ih ⟨c.l, f c.var (c.stk k).head?, c.stk⟩ hc
  | load f q ih => exact ih ⟨c.l, f c.var, c.stk⟩ hc
  | branch f q r ihq ihr =>
    cases hf : f c.var
    · simp only [aux, packRaw, hf, Bool.false_eq_true, ↓reduceIte, TM2.stepAux, Bool.cond_false]
      apply ihr c
      intro k
      have h := hc k
      simp only [pushes] at h
      omega
    · simp only [aux, packRaw, hf, ↓reduceIte, TM2.stepAux, Bool.cond_true]
      apply ihq c
      intro k
      have h := hc k
      simp only [pushes] at h
      omega
  | goto f => rfl
  | halt => rfl

def hold (p : Packed tm C) : Packed tm C :=
  match p.1 with
  | none => p
  | some l => aux tm C (tm.m l) p

theorem hold_correct (c : tm.Cfg)
    (hc : ∀ k, (c.stk k).length + pushBudget tm ≤ C + 1) :
    hold tm C (packRaw tm C c) = packRaw tm C (holdStep tm c) := by
  cases hl : c.l with
  | none => simp [hold, packRaw, holdStep, hl]
  | some l =>
    letI : Fintype tm.Λ := tm.ΛFin
    have hb : pushes (tm.m l) ≤ pushBudget tm := by
      change pushes (tm.m l) ≤ ∑ j : tm.Λ,pushes (tm.m j)
      exact Finset.single_le_sum (f := fun j : tm.Λ => pushes (tm.m j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    simpa [hold, packRaw, holdStep, hl] using
      aux_correct tm C (tm.m l) c (fun k => by have h := hc k; omega)

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.PackedStep
