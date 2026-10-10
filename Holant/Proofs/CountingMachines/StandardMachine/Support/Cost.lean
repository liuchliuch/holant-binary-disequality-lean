import Holant.Proofs.CountingMachines.StandardMachine.Support.Foundation
import Mathlib.Data.Fintype.EquivFin

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Primitive accounting for actual heterogeneous statements.
This observer is used only in proofs. It never appears as a machine instruction.
-/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open Turing
open scoped BigOperators
namespace HeterogeneousCost
variable {K Λ σ : Type} [DecidableEq K] {Γ : K → Type}
def budget : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => budget q + 1
  | .pop _ _ q => budget q + 1
  | .peek _ _ q => budget q + 1
  | .load _ q => budget q + 1
  | .branch _ q r => max (budget q) (budget r) + 1
  | .goto _ => 1
  | .halt => 1

def execute : TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → ℕ × TM2.Cfg Γ Λ σ
  | .push k f q,v,S => let r := execute q v (Function.update S k (f v :: S k)); (r.1+1,r.2)
  | .pop k f q,v,S => let r := execute q (f v (S k).head?) (Function.update S k (S k).tail); (r.1+1,r.2)
  | .peek k f q,v,S => let r := execute q (f v (S k).head?) S; (r.1+1,r.2)
  | .load f q,v,S => let r := execute q (f v) S; (r.1+1,r.2)
  | .branch f q s,v,S => let r := if f v then execute q v S else execute s v S; (r.1+1,r.2)
  | .goto f,v,S => (1,⟨some (f v),v,S⟩)
  | .halt,v,S => (1,⟨none,v,S⟩)

theorem result (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    (execute q v S).2 = TM2.stepAux q v S := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r hq hr => cases h : f v <;> simp [execute,TM2.stepAux,h,hq,hr]
  | goto f => rfl
  | halt => rfl

theorem cost_le (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    (execute q v S).1 ≤ budget q := by
  induction q generalizing v S with
  | push k f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | pop k f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | peek k f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | load f q ih => exact Nat.add_le_add_right (ih _ _) 1
  | branch f q r hq hr =>
    cases h : f v
    · simpa only [execute,budget,h,Bool.false_eq_true,ite_false] using
        Nat.add_le_add_right ((hr v S).trans (le_max_right _ _)) 1
    · simpa only [execute,budget,h,ite_true] using
        Nat.add_le_add_right ((hq v S).trans (le_max_left _ _)) 1
  | goto f => exact Nat.le_refl _
  | halt => exact Nat.le_refl _
end HeterogeneousCost

namespace BinaryMachine
variable (m : BinaryMachine)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

def primitiveBudget : ℕ :=
  (∑ l, (HeterogeneousCost.budget (m.core.m l) + HeterogeneousCost.budget (m.alternate l))) + 1

theorem core_budget_le (l : m.core.Λ) : HeterogeneousCost.budget (m.core.m l) + 1 ≤ m.primitiveBudget := by
  have hs : HeterogeneousCost.budget (m.core.m l) + HeterogeneousCost.budget (m.alternate l) ≤
    ∑ j, (HeterogeneousCost.budget (m.core.m j) + HeterogeneousCost.budget (m.alternate j)) :=
      Finset.single_le_sum (f := fun j => HeterogeneousCost.budget (m.core.m j) + HeterogeneousCost.budget (m.alternate j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  dsimp [primitiveBudget]
  omega

theorem alternate_budget_le (l : m.core.Λ) : HeterogeneousCost.budget (m.alternate l) + 1 ≤ m.primitiveBudget := by
  have hs : HeterogeneousCost.budget (m.core.m l) + HeterogeneousCost.budget (m.alternate l) ≤
    ∑ j, (HeterogeneousCost.budget (m.core.m j) + HeterogeneousCost.budget (m.alternate j)) :=
      Finset.single_le_sum (f := fun j => HeterogeneousCost.budget (m.core.m j) + HeterogeneousCost.budget (m.alternate j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  dsimp [primitiveBudget]
  omega

/-- A binary choice is charged once in addition to its chosen real statement.
Failed branch-log EOF is also charged; halted padding costs zero. -/
def transitionCost (s : List Bool × m.Config) : ℕ :=
  match s.2.l with
  | none => 0
  | some l => if m.split l then
      match s.1 with
      | [] => 1
      | b :: _ => (HeterogeneousCost.execute
          (if b then m.alternate l else m.core.m l) s.2.var s.2.stk).1 + 1
    else (HeterogeneousCost.execute (m.core.m l) s.2.var s.2.stk).1

theorem transitionCost_le (s : List Bool × m.Config) : m.transitionCost s ≤ m.primitiveBudget := by
  cases hl : s.2.l with
  | none => simp [transitionCost,hl]
  | some l =>
    cases hs : m.split l with
    | false =>
      have hc := HeterogeneousCost.cost_le (m.core.m l) s.2.var s.2.stk
      have hb := m.core_budget_le l
      simp only [transitionCost,hl,hs,Bool.false_eq_true,ite_false]
      omega
    | true =>
      cases hlog : s.1 with
      | nil => simp [transitionCost,hl,hs,hlog,primitiveBudget]
      | cons b rest =>
        cases b with
        | false =>
          have hc := HeterogeneousCost.cost_le (m.core.m l) s.2.var s.2.stk
          have hb := m.core_budget_le l
          simp only [transitionCost,hl,hs,hlog,ite_true,Bool.false_eq_true,ite_false]
          omega
        | true =>
          have hc := HeterogeneousCost.cost_le (m.alternate l) s.2.var s.2.stk
          have hb := m.alternate_budget_le l
          simp only [transitionCost,hl,hs,hlog,ite_true]
          omega

def primitiveCost : ℕ → List Bool × m.Config → ℕ
  | 0,_ => 0
  | t+1,s => m.transitionCost s +
      ((m.advance s).map (primitiveCost t)).getD 0

theorem primitiveCost_le (t : ℕ) (s : List Bool × m.Config) :
    m.primitiveCost t s ≤ t * m.primitiveBudget := by
  induction t generalizing s with
  | zero => simp [primitiveCost]
  | succ t ih =>
    have hc := m.transitionCost_le s
    cases hs : m.advance s with
    | none => simpa only [primitiveCost,hs,Option.map_none,Option.getD_none,Nat.add_zero,Nat.succ_mul] using
        hc.trans (Nat.le_add_left _ _)
    | some next =>
      have ht := ih next
      simpa only [primitiveCost,hs,Option.map_some,Option.getD_some,Nat.succ_mul,
        Nat.add_comm] using Nat.add_le_add hc ht

/-- Fixed unary one-hot symbol widths; these are finite constants of the
presentation. The branch log is a path observer and is not machine memory. -/
def symbolWidths : ℕ := ∑ k : m.core.K, (Fintype.card (m.core.Γ k) + 1)
def controlBits : ℕ := Fintype.card m.core.Λ + Fintype.card m.core.σ + 2
def storageBits (c : m.Config) : ℕ := m.controlBits +
  ∑ k : m.core.K, (c.stk k).length * (Fintype.card (m.core.Γ k) + 1)

/-- A literal finite-alphabet code, fixed at construction time. Each word has
one false terminator and an index-sized true prefix. -/
noncomputable def symbolCode {A : Type} [Fintype A] (a : A) : List Bool :=
  List.replicate (Fintype.equivFin A a).val true ++ [false]

theorem symbolCode_length {A : Type} [Fintype A] (a : A) :
    (symbolCode a).length ≤ Fintype.card A := by
  unfold symbolCode
  rw [List.length_append,List.length_replicate,List.length_singleton]
  exact Nat.succ_le_of_lt (Fintype.equivFin A a).isLt

theorem symbolCode_injective {A : Type} [Fintype A] :
    Function.Injective (symbolCode : A → List Bool) := by
  intro a b h
  apply (Fintype.equivFin A).injective
  apply Fin.ext
  have hl := congrArg List.length h
  simp only [symbolCode,List.length_append,List.length_replicate,List.length_singleton] at hl
  omega

noncomputable def labelCode : Option m.core.Λ → List Bool
  | none => [false]
  | some l => true :: symbolCode l

noncomputable def codedStorageBits (c : m.Config) : ℕ :=
  (m.labelCode c.l).length + (symbolCode c.var).length +
    ∑ k : m.core.K, ((c.stk k).flatMap (fun a => symbolCode a)).length

theorem wordCode_length {A : Type} [Fintype A] (xs : List A) :
    (xs.flatMap (fun a => symbolCode a)).length ≤ xs.length * (Fintype.card A + 1) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hc := (symbolCode_length a).trans (Nat.le_add_right (Fintype.card A) 1)
    simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul,Nat.add_comm]
      using Nat.add_le_add hc ih

theorem codedStorageBits_le (c : m.Config) : m.codedStorageBits c ≤ m.storageBits c := by
  have hl : (m.labelCode c.l).length ≤ Fintype.card m.core.Λ + 1 := by
    cases c.l with
    | none => simp [labelCode]
    | some l =>
      have h := symbolCode_length l
      simpa only [labelCode,List.length_cons,Nat.add_comm] using Nat.add_le_add_left h 1
  have hs := symbolCode_length c.var
  have hc : (m.labelCode c.l).length + (symbolCode c.var).length ≤ m.controlBits := by
    unfold controlBits
    omega
  exact Nat.add_le_add hc (Finset.sum_le_sum (fun k _ => wordCode_length (c.stk k)))

theorem storageBits_le (c : m.Config) (C : ℕ) (h : ∀ k, (c.stk k).length ≤ C) :
    m.storageBits c ≤ m.controlBits + C * m.symbolWidths := by
  unfold storageBits
  apply Nat.add_le_add_left
  unfold symbolWidths
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_right _ (h k))

end BinaryMachine
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
