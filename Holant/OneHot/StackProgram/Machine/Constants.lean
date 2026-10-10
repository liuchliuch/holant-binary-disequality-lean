import Holant.OneHot.StackProgram.Machine.Dispatch
import Holant.Complexity.FixedFieldMachines.Constant

/-! Fixed encoded constants are compiled to literal Boolean push syntax. The
loader never computes a semantic coefficient or encodes a field value at runtime.
The table and its correctness evidence are fixed before the bytecode is supplied.
-/
namespace Holant.OneHot.StackProgram.Machine.Constants
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt
variable {A V K Λ τ : Type} [DecidableEq K]

/-- The operational table consists solely of fixed Boolean words. -/
structure Table (A V : Type) (e : Encoding V Bool) (coeff : A → V) where
  words : A → List Bool
  correct : ∀ a, words a = e.encode (coeff a)

/-- Literal table lookup happens during finite-program construction. -/
def loadStmt (dst : K) (word : List Bool) (next : Λ) : Stmt K Λ τ :=
  FixedFieldMachines.Constant.pushWord dst
    (true :: Holant.Algebraic.frame word) (goto (fun _ => next))

/-- Actual encoded-list cons, preserving the complete existing stack suffix. -/
theorem loadStmt_exact (dst : K) (word : List Bool) (next : Λ)
    (memory : τ) (tapes : K → List Bool) :
    TM2.stepAux (loadStmt dst word next) (none, memory) tapes =
      cfg next memory (Function.update tapes dst
        (true :: Holant.Algebraic.frame word ++ tapes dst)) := by
  rw [loadStmt, FixedFieldMachines.Constant.pushWord_eval]
  rfl

omit [DecidableEq K] in
/-- The entire encoded constant, frame delimiter, list marker, and jump are charged. -/
theorem loadStmt_budget (dst : K) (word : List Bool) (next : Λ) :
    TM2Cost.budget (loadStmt (τ := τ) dst word next) = 2 * word.length + 3 := by
  simp [loadStmt, FixedFieldMachines.Constant.pushWord_budget, TM2Cost.budget]

/-- A fixed table gives a genuine finite Boolean-stack loader for each label. -/
abbrev machine {n : ℕ} (words : Fin n → List Bool) (a : Fin n) : BinaryCompose.Machine where
  K := Unit
  input := ()
  output := ()
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label then .halt else loadStmt () (words a) true

/-- Clean input/output correctness of literal prefix loading. No input is erased. -/
theorem machine_exact {n : ℕ} (words : Fin n → List Bool) (a : Fin n) (suffix : List Bool) :
    RunsExactly (machine words a).computer.step
      (initList (machine words a).computer suffix)
      (haltList (machine words a).computer (true :: Holant.Algebraic.frame (words a) ++ suffix)) 2 := by
  have first : (machine words a).computer.step
      (cfg false () (BinaryCompose.wordTape () suffix)) =
      some (cfg true () (BinaryCompose.wordTape ()
        (true :: Holant.Algebraic.frame (words a) ++ suffix))) := by
    change some (TM2.stepAux (loadStmt () (words a) true) (none, ()) _) = _
    rw [loadStmt_exact]
    rfl
  have last : (machine words a).computer.step
      (cfg true () (BinaryCompose.wordTape ()
        (true :: Holant.Algebraic.frame (words a) ++ suffix))) =
      some (haltList (machine words a).computer
        (true :: Holant.Algebraic.frame (words a) ++ suffix)) := by
    rw [BinaryCompose.Machine.halt_eq]
    rfl
  rw [BinaryCompose.Machine.init_eq]
  exact (runsExactly_one first).trans (runsExactly_one last)

/-- The fixed fieldword codec is retained literally in the machine output. -/
theorem table_stack_exact {n : ℕ} (e : Encoding V Bool) (coeff : Fin n → V)
    (table : Table (Fin n) V e coeff) (a : Fin n) (s : List V) :
    RunsExactly (machine table.words a).computer.step
      (initList (machine table.words a).computer ((stackEncoding e).encode s))
      (haltList (machine table.words a).computer ((stackEncoding e).encode (coeff a :: s))) 2 := by
  simpa only [table.correct, stackEncoding, framedListEncoding, framedListEncode, List.cons_append] using
    machine_exact table.words a ((stackEncoding e).encode s)

/-- A actual clean finite-machine witness; the value parameter is fixed in its
push syntax, and the linear output-size overhead is accounted separately. -/
noncomputable def computes {n : ℕ} (e : Encoding V Bool) (coeff : Fin n → V)
    (table : Table (Fin n) V e coeff) (a : Fin n) :
    BinaryCompose.Computes (stackEncoding e) (stackEncoding e) (fun s => coeff a :: s) where
  machine := machine table.words a
  time := 2
  outputs s :=
    { steps := 2
      evals_in_steps := table_stack_exact e coeff table a s
      steps_le_m := by simp }

end Holant.OneHot.StackProgram.Machine.Constants
