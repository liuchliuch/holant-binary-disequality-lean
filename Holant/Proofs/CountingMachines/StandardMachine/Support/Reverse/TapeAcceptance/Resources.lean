import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.TapeAcceptance.Counting

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The observer is charged as actual elementary syntax.
It adds no TM2 macro transition, split token, tape, or input byte. The bounded
reverse verifier's staging/clock/interpreter/cleanup costs are reused from the
existing full-program producer, now with this larger literal statement table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

theorem scan_budget (ks : List m.core.K) :
    HeterogeneousCost.budget (scan m ks) ≤ ks.length+2 := by
  induction ks with
  | nil => simp [scan,HeterogeneousCost.budget]
  | cons k ks ih =>
    by_cases hk : k = m.core.k₁ <;>
      simp only [scan,hk,ite_true,ite_false,HeterogeneousCost.budget,List.length_cons] <;> omega

theorem observer_budget : HeterogeneousCost.budget (observer m trueSymbol) ≤
    Fintype.card m.core.K+7 := by
  have hb := scan_budget m (keys m)
  have hl : (keys m).length = Fintype.card m.core.K := List.length_ofFn
  simp only [observer,HeterogeneousCost.budget]
  rw [max_eq_left (Nat.le_add_right _ 1)]
  omega

theorem observer_primitive (v : State m) (S : ∀ k, List (m.core.Γ k)) :
    (HeterogeneousCost.execute (observer m trueSymbol) v S).1 ≤ Fintype.card m.core.K+7 :=
  (HeterogeneousCost.cost_le _ _ _).trans (observer_budget m trueSymbol)

theorem statement_budget (q : m.core.Stmt) :
    HeterogeneousCost.budget (statement m trueSymbol q) ≤
      HeterogeneousCost.budget q+(Fintype.card m.core.K+7) := by
  induction q with
  | push k f q ih => simpa only [statement,HeterogeneousCost.budget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using Nat.add_le_add_right ih 1
  | pop k f q ih => simpa only [statement,HeterogeneousCost.budget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using Nat.add_le_add_right ih 1
  | peek k f q ih => simpa only [statement,HeterogeneousCost.budget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using Nat.add_le_add_right ih 1
  | load f q ih => simpa only [statement,HeterogeneousCost.budget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using Nat.add_le_add_right ih 1
  | branch f q r hq hr =>
    have hm : max (HeterogeneousCost.budget (statement m trueSymbol q))
        (HeterogeneousCost.budget (statement m trueSymbol r)) ≤
        max (HeterogeneousCost.budget q) (HeterogeneousCost.budget r)+(Fintype.card m.core.K+7) :=
      max_le (hq.trans (Nat.add_le_add_right (le_max_left _ _) _))
        (hr.trans (Nat.add_le_add_right (le_max_right _ _) _))
    simpa only [statement,HeterogeneousCost.budget,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using Nat.add_le_add_right hm 1
  | goto f => simp [statement,HeterogeneousCost.budget]
  | halt =>
    have h := observer_budget m trueSymbol
    simp only [statement,HeterogeneousCost.budget]
    omega

/-- A fixed finite register holds the actual popped output head, plus one Bool.
It is cleared before halt; its full one-hot finite control code is charged. -/
theorem state_card : Fintype.card (State m) =
    Fintype.card m.core.σ*((Fintype.card (m.core.Γ m.core.k₁)+1)*2) := by
  simp only [State,Fintype.card_prod,Fintype.card_option,Fintype.card_bool]

def capacityPolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.X+T*Polynomial.C (machine m trueSymbol).pushBudget
def primitivePolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  T*Polynomial.C (machine m trueSymbol).primitiveBudget
def bitsPolynomial (T : Polynomial ℕ) : Polynomial ℕ :=
  Polynomial.C (machine m trueSymbol).controlBits+
    capacityPolynomial m trueSymbol T*Polynomial.C (machine m trueSymbol).symbolWidths

/-- Every successful real prefix, including rejection and early halt, has
the original byte-length capacity bound. No capacity premise is supplied. -/
theorem prefix_capacity (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (next : List Bool × (machine m trueSymbol).Config)
    (hj : j ≤ T.eval word.length)
    (hr : (machine m trueSymbol).run j (log,initList (computer m trueSymbol) word) = some next) :
    ∀ k, (next.2.stk k).length ≤ (capacityPolynomial m trueSymbol T).eval word.length := by
  have hinit : ∀ k, ((initList (computer m trueSymbol) word).stk k).length ≤ word.length := by
    intro k
    simpa only [Function.iterate_zero_apply,Nat.zero_mul,Nat.add_zero] using
      Holant.LocalDrafts.CountingHardness.VerifierRun.run_stack_bound (computer m trueSymbol) word 0 k
  have hb := (machine m trueSymbol).run_stack_bound j _ _ word.length hinit hr
  have hm := Nat.mul_le_mul_right (machine m trueSymbol).pushBudget hj
  intro k
  simpa only [capacityPolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
    Polynomial.eval_C] using (hb k).trans (Nat.add_le_add_left hm word.length)

theorem prefix_primitive (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (hj : j ≤ T.eval word.length) :
    (machine m trueSymbol).primitiveCost j (log,initList (computer m trueSymbol) word) ≤
      (primitivePolynomial m trueSymbol T).eval word.length := by
  exact ((machine m trueSymbol).primitiveCost_le j _).trans
    (by simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using
      Nat.mul_le_mul_right (machine m trueSymbol).primitiveBudget hj)

theorem prefix_bits (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (log : List Bool) (j : ℕ) (next : List Bool × (machine m trueSymbol).Config)
    (hj : j ≤ T.eval word.length)
    (hr : (machine m trueSymbol).run j (log,initList (computer m trueSymbol) word) = some next) :
    (machine m trueSymbol).codedStorageBits next.2 ≤ (bitsPolynomial m trueSymbol T).eval word.length := by
  have hs := ((machine m trueSymbol).codedStorageBits_le next.2).trans
    ((machine m trueSymbol).storageBits_le next.2 _ (prefix_capacity m trueSymbol T word log j next hj hr))
  simpa only [bitsPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using hs

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
