import Holant.Complexity.WitnessCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs


namespace Holant.LocalDrafts.CountingHardness.VerifierRun

open Turing Computability Holant.Complexity
open scoped BigOperators

section Statement
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Number of syntactic pushes; summing both branches is a safe fixed bound. -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .pop _ _ q => pushes q
  | .peek _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ a b => pushes a + pushes b
  | .goto _ => 0
  | .halt => 0

theorem stepAux_stack_bound (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    ∀ k, ((TM2.stepAux q v S).stk k).length ≤ B + pushes q := by
  induction q generalizing v S B with
  | push j f q ih =>
    have hu : ∀ k, ((Function.update S j (f v :: S j)) k).length ≤ B + 1 := by
      intro k
      by_cases hk : k = j
      · subst k
        simpa using Nat.add_le_add_right (hS j) 1
      · simpa [hk] using Nat.le_trans (hS k) (Nat.le_add_right B 1)
    intro k
    have h := ih v (Function.update S j (f v :: S j)) (B + 1) hu k
    simpa [TM2.stepAux, pushes, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  | pop j f q ih =>
    have hu : ∀ k, ((Function.update S j (S j).tail) k).length ≤ B := by
      intro k
      by_cases hk : k = j
      · subst k
        have ht : (S j).tail.length ≤ (S j).length := by simp
        simpa using Nat.le_trans ht (hS j)
      · simpa [hk] using hS k
    exact ih (f v (S j).head?) (Function.update S j (S j).tail) B hu
  | peek j f q ih => exact ih (f v (S j).head?) S B hS
  | load f q ih => exact ih (f v) S B hS
  | branch f a b ha hb =>
    intro k
    cases h : f v <;> simp only [TM2.stepAux, h, Bool.cond_false, Bool.cond_true, pushes]
    · have hh := hb v S B hS k
      omega
    · have hh := ha v S B hS k
      omega
  | goto f => simpa [TM2.stepAux, pushes] using hS
  | halt => simpa [TM2.stepAux, pushes] using hS

end Statement

/-- Preserve the last configuration, rather than erasing it one step after halt. -/
def holdStep (tm : FinTM2) (c : tm.Cfg) : tm.Cfg :=
  match c.l with
  | none => c
  | some label => TM2.stepAux (tm.m label) c.var c.stk

@[simp] theorem holdStep_halt (tm : FinTM2) (out : List (tm.Γ tm.k₁)) :
    holdStep tm (haltList tm out) = haltList tm out := rfl

theorem holdStep_of_step (tm : FinTM2) {c d : tm.Cfg} (h : tm.step c = some d) :
    holdStep tm c = d := by
  rcases c with ⟨label, state, stackWords⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at h
  | some label => exact Option.some.inj h

/-- A successful library run agrees with the same number of held transitions. -/
theorem iterate_hold_of_some (tm : FinTM2) (t : ℕ) (c d : tm.Cfg)
    (h : (fun z : Option tm.Cfg => z.bind tm.step)^[t] (some c) = some d) :
    (holdStep tm)^[t] c = d := by
  induction t generalizing c with
  | zero => exact Option.some.inj h
  | succ t ih =>
    rw [Function.iterate_succ_apply] at h ⊢
    cases hs : tm.step c with
    | none =>
      have hn : (fun z : Option tm.Cfg => z.bind tm.step)^[t] none = none := by
        exact Function.iterate_fixed
          (f := fun z : Option tm.Cfg => z.bind tm.step) rfl t
      simp only [Option.bind_some, hs, hn] at h
      cases h
    | some next =>
      have hh : (holdStep tm) c = next := holdStep_of_step tm hs
      rw [hh]
      apply ih next
      simpa only [Option.bind_some, hs] using h

/-- Padding to the advertised time bound does not add accepting histories. -/
theorem outputs_at_bound (tm : FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (T : ℕ)
    (h : TM2OutputsInTime tm input (some output) T) :
    (holdStep tm)^[T] (initList tm input) = haltList tm output := by
  have hs := iterate_hold_of_some tm h.steps (initList tm input) (haltList tm output)
    h.evals_in_steps
  have hpad : ∀ t, (holdStep tm)^[t] (haltList tm output) = haltList tm output := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => simpa [Function.iterate_succ_apply] using ih
  calc
    (holdStep tm)^[T] (initList tm input) =
        (holdStep tm)^[(T - h.steps) + h.steps] (initList tm input) := by
      rw [Nat.sub_add_cancel h.steps_le_m]
    _ = (holdStep tm)^[T - h.steps] ((holdStep tm)^[h.steps] (initList tm input)) :=
      Function.iterate_add_apply _ _ _ _
    _ = haltList tm output := by rw [hs, hpad]

local instance (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin

def pushBudget (tm : FinTM2) : ℕ := ∑ label, pushes (tm.m label)

theorem holdStep_stack_bound (tm : FinTM2) (c : tm.Cfg) (B : ℕ)
    (hc : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, ((holdStep tm c).stk k).length ≤ B + pushBudget tm := by
  cases hl : c.l with
  | none => simpa [holdStep, hl] using fun k => Nat.le_trans (hc k) (Nat.le_add_right _ _)
  | some label =>
    have hp : pushes (tm.m label) ≤ pushBudget tm := by
      change pushes (tm.m label) ≤ ∑ j, pushes (tm.m j)
      exact Finset.single_le_sum (f := fun j : tm.Λ => pushes (tm.m j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)
    intro k
    have hs := stepAux_stack_bound (tm.m label) c.var c.stk B hc k
    simpa only [holdStep, hl] using le_trans hs (Nat.add_le_add_left hp B)

theorem run_stack_bound (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (t : ℕ) :
    ∀ k, (((holdStep tm)^[t] (initList tm input)).stk k).length ≤
      input.length + t * pushBudget tm := by
  induction t with
  | zero =>
    intro k
    rw [Function.iterate_zero_apply, Nat.zero_mul, Nat.add_zero]
    by_cases hk : k = tm.k₀
    · subst k
      simp [initList]
    · simp [initList, hk]
  | succ t ih =>
    have hs := holdStep_stack_bound tm ((holdStep tm)^[t] (initList tm input))
      (input.length + t * pushBudget tm) ih
    simpa [Function.iterate_succ_apply', Nat.succ_mul, Nat.add_assoc] using hs

/-- Local tableau equations over actual machine configurations. -/
def IsTrajectory (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (T : ℕ)
    (rows : Fin (T + 1) → tm.Cfg) : Prop :=
  rows 0 = initList tm input ∧
    ∀ i : Fin T, rows i.succ = holdStep tm (rows i.castSucc)

def trajectory (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (T : ℕ) :
    Fin (T + 1) → tm.Cfg := fun i => (holdStep tm)^[i.val] (initList tm input)

theorem trajectory_valid (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (T : ℕ) :
    IsTrajectory tm input T (trajectory tm input T) := by
  refine ⟨rfl, ?_⟩
  intro i
  exact Function.iterate_succ_apply' _ _ _

theorem trajectory_unique (tm : FinTM2) (input : List (tm.Γ tm.k₀)) (T : ℕ)
    (rows : Fin (T + 1) → tm.Cfg) (h : IsTrajectory tm input T rows) :
    rows = trajectory tm input T := by
  have hall : ∀ (j : ℕ) (hj : j < T + 1),
      rows ⟨j, hj⟩ = (holdStep tm)^[j] (initList tm input) := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact h.1
    | succ j ih =>
      intro hj
      have hit : j < T := by omega
      have hp := ih (by omega)
      have hs := h.2 ⟨j, hit⟩
      change rows ⟨j + 1, hj⟩ = holdStep tm (rows ⟨j, by omega⟩) at hs
      rw [hs, hp]
      exact (Function.iterate_succ_apply' _ _ _).symm
  funext i
  exact hall i.val i.isLt

section Witness
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

def witnessLength (a : α) : ℕ := w.witnessLength.eval (ea.encode a).length

def inputWord (a : α) (bits : Fin (witnessLength w a) → Bool) :
    List (w.verifier.tm.Γ w.verifier.tm.k₀) :=
  ((encodingProd ea (encodingList Bool)).encode (a, List.ofFn bits)).map
    w.verifier.inputAlphabet.symm

@[simp] theorem inputWord_length (a : α) (bits : Fin (witnessLength w a) → Bool) :
    (inputWord w a bits).length = (ea.encode a).length + witnessLength w a := by
  simp [inputWord, encodingList]

/-- One fixed polynomial in the original encoded input length. -/
noncomputable def horizonPolynomial : Polynomial ℕ :=
  w.verifier.time.comp (Polynomial.X + w.witnessLength)

noncomputable def horizon (a : α) : ℕ := (horizonPolynomial w).eval (ea.encode a).length

theorem verifier_terminal (a : α) (bits : Fin (witnessLength w a) → Bool) :
    (holdStep w.verifier.tm)^[horizon w a] (initList w.verifier.tm (inputWord w a bits)) =
      haltList w.verifier.tm [w.verifier.outputAlphabet.symm
        (Sum.inr (w.accept (a, List.ofFn bits)))] := by
  apply outputs_at_bound
  have hlen : (List.ofFn bits).length =
      w.witnessLength.eval (ea.encode a).length := List.length_ofFn
  have htime : w.verifier.time.eval
      (((encodingProd ea (encodingList Bool)).encode (a,List.ofFn bits)).length) =
        horizon w a := by
    rw [encodingProd_length]
    change w.verifier.time.eval ((ea.encode a).length + (List.ofFn bits).length) = horizon w a
    rw [hlen]
    simp only [horizon,horizonPolynomial,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_X]
  have ht := w.verifier.outputsFun (a, List.ofFn bits)
  change TM2OutputsInTime w.verifier.tm (inputWord w a bits)
    (some [w.verifier.outputAlphabet.symm (Sum.inr (w.accept (a,List.ofFn bits)))])
    (w.verifier.time.eval
      (((encodingProd ea (encodingList Bool)).encode (a,List.ofFn bits)).length)) at ht
  rw [htime] at ht
  exact ht

noncomputable def capacityPolynomial : Polynomial ℕ :=
  Polynomial.X + w.witnessLength +
    horizonPolynomial w * Polynomial.C (pushBudget w.verifier.tm)

theorem verifier_stack_capacity (a : α) (bits : Fin (witnessLength w a) → Bool)
    (i : Fin (horizon w a + 1)) (k : w.verifier.tm.K) :
    ((trajectory w.verifier.tm (inputWord w a bits) (horizon w a) i).stk k).length ≤
      (capacityPolynomial w).eval (ea.encode a).length := by
  have hb := run_stack_bound w.verifier.tm (inputWord w a bits) i.val k
  have hi : i.val ≤ horizon w a := by omega
  have hm := Nat.mul_le_mul_right (pushBudget w.verifier.tm) hi
  simp only [inputWord_length] at hb
  simpa [trajectory, capacityPolynomial, horizon, witnessLength] using
    le_trans hb (Nat.add_le_add_left hm ((ea.encode a).length + witnessLength w a))

end Witness
end Holant.LocalDrafts.CountingHardness.VerifierRun
