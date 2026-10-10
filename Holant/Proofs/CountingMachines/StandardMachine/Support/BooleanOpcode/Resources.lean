import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanOpcode.Simulation

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The real fixed-depth symbol routines have physical
costs derived from their literal Boolean instruction tables. No primitive cost,
symbol capacity, or simulator correctness premise is constructor metadata. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Compiler
open Turing Computability Holant.Complexity
open scoped BigOperators
variable (m : BinaryMachine)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin

def widthBound : ℕ := ∑ k : m.core.K, Code.width m k
def coefficient : ℕ := 4*widthBound m+6

theorem width_le (k : m.core.K) : Code.width m k ≤ widthBound m :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

theorem coefficient_one : 1 ≤ coefficient m := by simp [coefficient]
theorem block_overhead (k : m.core.K) : 4*Code.width m k+4 ≤ coefficient m := by
  have h := width_le m k
  unfold coefficient
  omega

theorem statement_budget (q : m.core.Stmt) :
    HeterogeneousCost.budget (statement m q) ≤ coefficient m*HeterogeneousCost.budget q := by
  induction q with
  | push k f q ih =>
    have hw := block_overhead m k
    rw [statement,Block.pushVector_budget,HeterogeneousCost.budget,Nat.mul_add,Nat.mul_one]
    omega
  | pop k f q ih =>
    let leaf := fun head => TM2.Stmt.load (fun v : State m => Block.clear m (f v.1 head)) (statement m q)
    have hl : ∀ head, HeterogeneousCost.budget (leaf head) ≤ HeterogeneousCost.budget (statement m q)+1 :=
      fun _ => Nat.le_refl _
    have hb := Block.read_budget m k leaf _ hl (Code.width m k) []
    have hw := block_overhead m k
    change HeterogeneousCost.budget (Block.read m k leaf (Code.width m k) []) ≤ _
    simp only [HeterogeneousCost.budget,Nat.mul_add,Nat.mul_one]
    omega
  | peek k f q ih =>
    let leaf := fun head => TM2.Stmt.load (fun v : State m => Block.clear m (f v.1 head)) (statement m q)
    let restored := fun head : Option (m.core.Γ k) => head.elim (leaf none) (fun a =>
      Block.pushVector m k (Code.width m k) (fun i _ => Code.bit m k a i) (leaf (some a)))
    have hl : ∀ head, HeterogeneousCost.budget (restored head) ≤
        Code.width m k+HeterogeneousCost.budget (statement m q)+1 := by
      intro head
      cases head with
      | none => simp [restored,leaf,HeterogeneousCost.budget]
      | some a => simp [restored,leaf,Block.pushVector_budget,HeterogeneousCost.budget,Nat.add_assoc]
    have hb := Block.read_budget m k restored _ hl (Code.width m k) []
    have hw := block_overhead m k
    change HeterogeneousCost.budget (Block.read m k restored (Code.width m k) []) ≤ _
    simp only [HeterogeneousCost.budget,Nat.mul_add,Nat.mul_one]
    omega
  | load f q ih =>
    have ho := coefficient_one m
    simp only [statement,HeterogeneousCost.budget,Nat.mul_add,Nat.mul_one]
    omega
  | branch f q r hq hr =>
    have hm : max (HeterogeneousCost.budget (statement m q)) (HeterogeneousCost.budget (statement m r)) ≤
        coefficient m*max (HeterogeneousCost.budget q) (HeterogeneousCost.budget r) :=
      max_le (hq.trans (Nat.mul_le_mul_left _ (le_max_left _ _)))
        (hr.trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    have ho := coefficient_one m
    simp only [statement,HeterogeneousCost.budget,Nat.mul_add,Nat.mul_one]
    omega
  | goto f => simpa only [statement,HeterogeneousCost.budget,Nat.mul_one] using coefficient_one m
  | halt => simpa only [statement,HeterogeneousCost.budget,Nat.mul_one] using coefficient_one m

theorem statement_primitive (q : m.core.Stmt) (v : State m) (S : m.core.K → List Bool) :
    (HeterogeneousCost.execute (statement m q) v S).1 ≤
      coefficient m*HeterogeneousCost.budget q :=
  (HeterogeneousCost.cost_le _ _ _).trans (statement_budget m q)

theorem coded_capacity (c : m.Config) (B : ℕ) (h : ∀ k, (c.stk k).length ≤ B) :
    ∀ k, ((cfg m c).stk k).length ≤ widthBound m*B := by
  intro k
  change (Code.word m k (c.stk k)).length ≤ _
  rw [Code.word_length]
  exact (Nat.mul_le_mul_left _ (h k)).trans (Nat.mul_le_mul_right B (width_le m k))

def primitivePolynomial (T : Polynomial ℕ) : Polynomial ℕ := T*Polynomial.C (machine m).primitiveBudget
def capacityPolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (widthBound m)*Polynomial.X+T*Polynomial.C (machine m).pushBudget
def bitsPolynomial (T : Polynomial ℕ) : Polynomial ℕ := Polynomial.C (machine m).controlBits+
  capacityPolynomial m T*Polynomial.C (machine m).symbolWidths

/-- Real Boolean execution prefixes from an actual Boolean initList. Its raw
input word here is explicitly the serialized source input; the separate
original-byte preparation obligation is not silently hidden by this theorem. -/
theorem prefix_capacity (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (next : List Bool × (machine m).Config)
    (hj : j ≤ T.eval word.length)
    (hr : (machine m).run j (log,initList (computer m) (Code.word m m.core.k₀ word)) = some next) :
    ∀ k, (next.2.stk k).length ≤ (capacityPolynomial m T).eval word.length := by
  have hinit : ∀ k, ((initList (computer m) (Code.word m m.core.k₀ word)).stk k).length ≤
      widthBound m*word.length := by
    intro k
    have hk := Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (computer m) (Code.word m m.core.k₀ word) 0 k
    simp only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero,Code.word_length] at hk
    exact hk.trans (Nat.mul_le_mul_right _ (width_le m m.core.k₀))
  have hb := (machine m).run_stack_bound j _ _ _ hinit hr
  have hm := Nat.mul_le_mul_right (machine m).pushBudget hj
  intro k
  simpa only [capacityPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    using (hb k).trans (Nat.add_le_add_left hm (widthBound m*word.length))

theorem prefix_primitive (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (hj : j ≤ T.eval word.length) :
    (machine m).primitiveCost j (log,initList (computer m) (Code.word m m.core.k₀ word)) ≤
      (primitivePolynomial m T).eval word.length :=
  ((machine m).primitiveCost_le j _).trans (by
    simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_right (machine m).primitiveBudget hj)

theorem prefix_bits (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (next : List Bool × (machine m).Config)
    (hj : j ≤ T.eval word.length)
    (hr : (machine m).run j (log,initList (computer m) (Code.word m m.core.k₀ word)) = some next) :
    (machine m).codedStorageBits next.2 ≤ (bitsPolynomial m T).eval word.length := by
  have hs := ((machine m).codedStorageBits_le next.2).trans
    ((machine m).storageBits_le next.2 _ (prefix_capacity m T word log j next hj hr))
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using hs

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanOpcode.Compiler
