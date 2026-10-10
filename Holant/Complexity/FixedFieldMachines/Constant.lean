import Holant.Complexity.FixedFieldMachines.PairEncoding
import Holant.Complexity.StackProtocol

/-! Fixed constants compile to finite push syntax, with a proved primitive budget.
Input erasure is a real symbol-by-symbol loop. The word is fixed before the
input is supplied, and never occurs in finite control memory. -/
namespace Holant.Complexity.FixedFieldMachines
namespace Constant
open Turing Computability BinaryCompose StackProtocol
variable {K Λ σ : Type} [DecidableEq K]

def pushWord (key : K) : List Bool → TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ σ
  | [], next => next
  | bit :: word, next => pushWord key word (.push key (fun _ => bit) next)

theorem pushWord_eval (key : K) (word : List Bool)
    (next : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ) (tapes : K → List Bool) :
    TM2.stepAux (pushWord key word next) state tapes =
      TM2.stepAux next state (Function.update tapes key (word ++ tapes key)) := by
  induction word generalizing next with
  | nil => simp [pushWord]
  | cons bit word ih =>
    rw [pushWord, ih]
    simp [TM2.stepAux, Function.update_idem]

omit [DecidableEq K] in
theorem pushWord_budget (key : K) (word : List Bool)
    (next : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (pushWord key word next) = word.length + TM2Cost.budget next := by
  induction word generalizing next with
  | nil => simp [pushWord]
  | cons bit word ih => simp [pushWord, ih, TM2Cost.budget, Nat.add_assoc, Nat.add_comm]

abbrev machine (word : List Bool) : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label then pushWord () word .halt else clearStmt () false true

theorem exact_run (input word : List Bool) :
    RunsExactly (machine word).computer.step (initList (machine word).computer input)
      (haltList (machine word).computer word) (input.length + 2) := by
  have first := clear_exact (machine word).computer.step () false true
    (executesAt_tm2 _ _ _ rfl) () (wordTape () input)
  have hu : Function.update (wordTape () input) () [] = wordTape () [] := by
    funext k; cases k; rfl
  rw [hu] at first
  have last : (machine word).computer.step (cfg true () (wordTape () [])) =
      some (haltList (machine word).computer word) := by
    rw [Machine.halt_eq]
    dsimp [FinTM2.step, TM2.step, machine, cfg]
    rw [pushWord_eval]
    simp [TM2.stepAux, wordTape]
    rfl
  have run := first.trans (runsExactly_one last)
  rw [Machine.init_eq]
  simpa [cfg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

/-- Both input deletion and fixed constant loading have explicit primitive bounds. -/
theorem program_budget (word : List Bool) (label : Bool) :
    TM2Cost.budget ((machine word).program label) ≤ word.length + 4 := by
  cases label <;> simp [machine, pushWord_budget, TM2Cost.budget]

end Constant

open Computability BinaryCompose
noncomputable def constantComputes {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)
    (b : β) : Computes ea eb (fun _ => b) where
  machine := Constant.machine (eb.encode b)
  time := Polynomial.X + 2
  outputs a :=
    { steps := (ea.encode a).length + 2
      evals_in_steps := Constant.exact_run _ _
      steps_le_m := by simp }

end Holant.Complexity.FixedFieldMachines
