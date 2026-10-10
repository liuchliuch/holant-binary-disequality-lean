import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Counting

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Whole raw-input bounds, including rejection and cleanup.
All observers below consume the same finite code and literal original bytes.
No new cost executor, capacity input or Boolean machine-representation theorem
is introduced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
open Turing Holant.Complexity
variable (m : BinaryMachine) (T : Polynomial ℕ) (acceptControl : m.core.σ → Bool)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

def capacityPolynomial : Polynomial ℕ :=
  Polynomial.X+timePolynomial m T acceptControl*
    Polynomial.C (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl))
def primitivePolynomial : Polynomial ℕ :=
  timePolynomial m T acceptControl*Polynomial.C (deterministic m T acceptControl).primitiveBudget
def bitsPolynomial : Polynomial ℕ :=
  Polynomial.C (deterministic m T acceptControl).controlBits+
    capacityPolynomial m T acceptControl*Polynomial.C (deterministic m T acceptControl).symbolWidths

theorem prefix_exists (t j : ℕ) (c d : (computer m T acceptControl).Cfg)
    (h : (fun p => p.bind (computer m T acceptControl).step)^[t] (some c) = some d)
    (hj : j ≤ t) :
    ∃ next, (fun p => p.bind (computer m T acceptControl).step)^[j] (some c) = some next := by
  cases hp : (fun p => p.bind (computer m T acceptControl).step)^[j] (some c) with
  | some next => exact ⟨next,rfl⟩
  | none =>
    have hn : (fun p : Option (computer m T acceptControl).Cfg =>
        p.bind (computer m T acceptControl).step)^[t-j] none = none :=
      Function.iterate_fixed (f := fun p : Option (computer m T acceptControl).Cfg =>
        p.bind (computer m T acceptControl).step) rfl (t-j)
    rw [show t = (t-j)+j by omega,Function.iterate_add_apply,hp,hn] at h
    cases h

theorem prefix_capacity (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (j : ℕ) (next : (computer m T acceptControl).Cfg)
    (hj : j ≤ (outputs m T acceptControl word bits).steps)
    (hr : (fun p => p.bind (computer m T acceptControl).step)^[j]
      (some (initList (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) = some next) :
    ∀ k, (next.stk k).length ≤ (capacityPolynomial m T acceptControl).eval (word.length+bits.length) := by
  have hhold := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (computer m T acceptControl) j _ _ hr
  have htime := (outputs m T acceptControl word bits).steps_le_m
  have hmul := Nat.mul_le_mul_right (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl))
    (hj.trans htime)
  intro k
  have h := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (computer m T acceptControl)
    (word.map Sum.inl++bits.map Sum.inr) j k
  rw [hhold] at h
  simp only [List.length_append, List.length_map] at h
  simpa only [capacityPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_C,List.length_append,List.length_map] using
    h.trans (Nat.add_le_add_left hmul (word.length+bits.length))

theorem prefix_primitive (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (j : ℕ) (hj : j ≤ (outputs m T acceptControl word bits).steps) :
    (deterministic m T acceptControl).primitiveCost j
      ([],initList (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr)) ≤
        (primitivePolynomial m T acceptControl).eval (word.length+bits.length) := by
  have ht := hj.trans (outputs m T acceptControl word bits).steps_le_m
  exact ((deterministic m T acceptControl).primitiveCost_le j _).trans
    (by simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_right (deterministic m T acceptControl).primitiveBudget ht)

theorem prefix_bits (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (j : ℕ) (next : (computer m T acceptControl).Cfg)
    (hj : j ≤ (outputs m T acceptControl word bits).steps)
    (hr : (fun p => p.bind (computer m T acceptControl).step)^[j]
      (some (initList (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) = some next) :
    (deterministic m T acceptControl).codedStorageBits next ≤
      (bitsPolynomial m T acceptControl).eval (word.length+bits.length) := by
  have hc := prefix_capacity m T acceptControl word bits j next hj hr
  have h := ((deterministic m T acceptControl).codedStorageBits_le next).trans
    ((deterministic m T acceptControl).storageBits_le next _ hc)
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using h

/-- A path inside one actual statement, ending before or after any elementary
stack/state action. Branch constructors require the selected actual Bool test.
This is proof data, not an executor or a machine operation. -/
inductive InstructionPrefix : (computer m T acceptControl).Stmt →
    State m T → (∀ k, List (Alphabet m T k)) →
      State m T → (∀ k, List (Alphabet m T k)) → Prop
  | here q v S : InstructionPrefix q v S v S
  | push k f q v S u U :
      InstructionPrefix q v (Function.update S k (f v::S k)) u U →
        InstructionPrefix (.push k f q) v S u U
  | pop k f q v S u U :
      InstructionPrefix q (f v (S k).head?) (Function.update S k (S k).tail) u U →
        InstructionPrefix (.pop k f q) v S u U
  | peek k f q v S u U : InstructionPrefix q (f v (S k).head?) S u U →
      InstructionPrefix (.peek k f q) v S u U
  | load f q v S u U : InstructionPrefix q (f v) S u U →
      InstructionPrefix (.load f q) v S u U
  | branch_true f q r v S u U : f v = true → InstructionPrefix q v S u U →
      InstructionPrefix (.branch f q r) v S u U
  | branch_false f q r v S u U : f v = false → InstructionPrefix r v S u U →
      InstructionPrefix (.branch f q r) v S u U

theorem instruction_capacity (q : (computer m T acceptControl).Stmt) (v u : State m T)
    (S U : ∀ k, List (Alphabet m T k)) (h : InstructionPrefix m T acceptControl q v S u U)
    (B : ℕ) (hS : ∀ k, (S k).length ≤ B) :
    ∀ k, (U k).length ≤ B+Holant.LocalDrafts.CountingHardness.VerifierRun.pushes q := by
  induction h generalizing B with
  | here q v S => exact fun k => (hS k).trans (Nat.le_add_right _ _)
  | push k f q v S u U h ih =>
    have hu : ∀ j, ((Function.update S k (f v::S k)) j).length ≤ B+1 := by
      intro j
      by_cases hj : j = k
      · subst j; simpa using Nat.add_le_add_right (hS k) 1
      · simpa [hj] using (hS j).trans (Nat.le_add_right B 1)
    simpa only [Holant.LocalDrafts.CountingHardness.VerifierRun.pushes,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (B+1) hu
  | pop k f q v S u U h ih =>
    have hu : ∀ j, ((Function.update S k (S k).tail) j).length ≤ B := by
      intro j
      by_cases hj : j = k
      · subst j
        have ht : (S k).tail.length ≤ (S k).length := by simp
        simpa using ht.trans (hS k)
      · simpa [hj] using hS j
    exact ih B hu
  | peek k f q v S u U h ih => exact ih B hS
  | load f q v S u U h ih => exact ih B hS
  | branch_true f q r v S u U hf h ih =>
    intro k
    exact (ih B hS k).trans (by simp only [Holant.LocalDrafts.CountingHardness.VerifierRun.pushes]; omega)
  | branch_false f q r v S u U hf h ih =>
    intro k
    exact (ih B hS k).trans (by simp only [Holant.LocalDrafts.CountingHardness.VerifierRun.pushes]; omega)

theorem internal_bits (word : List (m.core.Γ m.core.k₀)) (bits : List Bool)
    (j : ℕ) (next : (computer m T acceptControl).Cfg)
    (hj : j < (outputs m T acceptControl word bits).steps)
    (hr : (fun p => p.bind (computer m T acceptControl).step)^[j]
      (some (initList (computer m T acceptControl) (word.map Sum.inl++bits.map Sum.inr))) = some next)
    (l : Label m T) (u : State m T) (U : ∀ k, List (Alphabet m T k))
    (h : InstructionPrefix m T acceptControl (program m T acceptControl l) next.var next.stk u U)
    (control : Option (Label m T)) :
    (deterministic m T acceptControl).codedStorageBits ⟨control,u,U⟩ ≤
      (bitsPolynomial m T acceptControl).eval (word.length+bits.length) := by
  have hhold := Holant.LocalDrafts.CountingHardness.VerifierRun.iterate_hold_of_some (computer m T acceptControl) j _ _ hr
  have hs : ∀ k, (next.stk k).length ≤ word.length+bits.length+
      j*Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl) := by
    intro k
    have hk := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (computer m T acceptControl)
      (word.map Sum.inl++bits.map Sum.inr) j k
    simpa only [hhold,List.length_append,List.length_map] using hk
  have hp : Holant.LocalDrafts.CountingHardness.VerifierRun.pushes (program m T acceptControl l) ≤
      Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl) :=
    Finset.single_le_sum (f := fun j : Label m T => Holant.LocalDrafts.CountingHardness.VerifierRun.pushes (program m T acceptControl j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  have ht : j+1 ≤ (timePolynomial m T acceptControl).eval (word.length+bits.length) :=
    (Nat.succ_le_of_lt hj).trans (outputs m T acceptControl word bits).steps_le_m
  have hU : ∀ k, (U k).length ≤ (capacityPolynomial m T acceptControl).eval (word.length+bits.length) := by
    intro k
    have hu := instruction_capacity m T acceptControl _ _ _ _ _ h _ hs k
    have hm := Nat.mul_le_mul_right (Holant.LocalDrafts.CountingHardness.VerifierRun.pushBudget (computer m T acceptControl)) ht
    simp only [capacityPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [Nat.succ_mul] at hm
    omega
  have hb := ((deterministic m T acceptControl).codedStorageBits_le ⟨control,u,U⟩).trans
    ((deterministic m T acceptControl).storageBits_le ⟨control,u,U⟩ _ hU)
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using hb

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Staging.Program
