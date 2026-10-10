import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# Actual Boolean-table access and update by a physical unary index

The machine scans one data bit per index token, stores the visited prefix on a
scratch stack, reads or edits the selected bit, and restores the whole prefix.
Every index test, bit read, optional write, and restoration step is accounted for.
The three possible edit modes are finite; no list lookup occurs in a callback.
-/
open Holant.Complexity Holant.Complexity.GraphPreprocessing

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.BitTable
open Turing Computability StackProtocol
open Turing.TM2.Stmt

def scanStmt (mode : Option Bool) : Stmt (Fin 4) (Fin 4) Unit :=
  pop 1 (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (pop 0 (fun v bit => (bit, v.2))
        (branch (fun v => v.1.isSome)
          (push 2 (fun v => v.1.getD false) (load (fun _ => (none, ())) (goto (fun _ => 0))))
          (load (fun _ => (none, ())) (goto (fun _ => 3)))))
      (pop 0 (fun v bit => (bit, v.2))
        (branch (fun v => v.1.isSome)
          (push 0 (fun v => mode.getD (v.1.getD false))
            (push 3 (fun v => v.1.getD false) (load (fun _ => (none, ())) (goto (fun _ => 1)))))
          (load (fun _ => (none, ())) (goto (fun _ => 3))))))

abbrev machine (mode : Option Bool) : BinaryCompose.Machine where
  K := Fin 4
  input := 0
  output := 3
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then scanStmt mode
    else if label = 1 then copyMoveStmt 2 0 1 2 else .halt

def tapes (table index scratch output : List Bool) : Fin 4 → List Bool := ![table, index, scratch, output]
def config (label : Fin 4) (table index scratch output : List Bool) : Cfg (Fin 4) (Fin 4) Unit :=
  cfg label () (tapes table index scratch output)

theorem scan_cons (mode : Option Bool) (bit token : Bool) (table index scratch output : List Bool) :
    (machine mode).computer.step (config 0 (bit :: table) (token :: index) scratch output) =
      some (config 0 table index (bit :: scratch) output) := by
  simp [FinTM2.step, TM2.step, machine, scanStmt, config, cfg, TM2.stepAux, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem scan_select (mode : Option Bool) (bit : Bool) (table scratch output : List Bool) :
    (machine mode).computer.step (config 0 (bit :: table) [] scratch output) =
      some (config 1 (mode.getD bit :: table) [] scratch (bit :: output)) := by
  simp [FinTM2.step, TM2.step, machine, scanStmt, config, cfg, TM2.stepAux, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem scan_missing (mode : Option Bool) (index scratch output : List Bool) :
    (machine mode).computer.step (config 0 [] index scratch output) =
      some (config 3 [] index.tail scratch output) := by
  cases index <;> simp [FinTM2.step, TM2.step, machine, scanStmt, config, cfg, TM2.stepAux, tapes]
  all_goals congr 2; funext k; fin_cases k <;> rfl

theorem restore_exact (mode : Option Bool) (table scratch output : List Bool) :
    RunsExactly (machine mode).computer.step (config 1 table [] scratch output)
      (config 2 (scratch.reverse ++ table) [] [] output) (scratch.length + 1) := by
  have hr : ExecutesAt (machine mode).computer.step (1 : Fin 4) (copyMoveStmt 2 0 1 2) := by intro state tapes; rfl
  have h := Frame.restore_exact (1 : Fin 4) 0 2 (by decide) (machine mode).computer.step 1 2 hr ()
    (tapes [] [] [] output) [] table scratch
  convert h using 1 <;> unfold config <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

/-- The scan consumes exactly one token and data bit per preceding table cell. -/
theorem scan_prefix (mode : Option Bool) (pre : List Bool) (bit : Bool) (tail scratch output : List Bool) :
    RunsExactly (machine mode).computer.step
      (config 0 (pre ++ bit :: tail) (List.replicate pre.length true) scratch output)
      (config 1 (mode.getD bit :: tail) [] (pre.reverse ++ scratch) (bit :: output)) (pre.length + 1) := by
  induction pre generalizing scratch with
  | nil => simpa using runsExactly_one (scan_select mode bit tail scratch output)
  | cons a pre ih =>
    have h := (runsExactly_one (scan_cons mode a true (pre ++ bit :: tail)
      (List.replicate pre.length true) scratch output)).trans (ih (a :: scratch))
    simpa [List.replicate_succ, List.reverse_cons, List.append_assoc] using h

/-- Exact returning read/update with the entire table restored except its selected cell. -/
theorem access_exact (mode : Option Bool) (pre : List Bool) (bit : Bool) (tail output : List Bool) :
    RunsExactly (machine mode).computer.step
      (config 0 (pre ++ bit :: tail) (List.replicate pre.length true) [] output)
      (config 2 (pre ++ mode.getD bit :: tail) [] [] (bit :: output)) (2 * (pre.length + 1)) := by
  have first := scan_prefix mode pre bit tail [] output
  simp only [List.append_nil] at first
  have h := first.trans (restore_exact mode (mode.getD bit :: tail) pre.reverse (bit :: output))
  simpa [Nat.two_mul] using h

/-- Stored indexes are physical unary words, and access costs only their length. -/
theorem get_exact (mode : Option Bool) (table : List Bool) (i : Fin table.length) (output : List Bool) :
    RunsExactly (machine mode).computer.step (config 0 table (List.replicate i.val true) [] output)
      (config 2 (table.set i.val (mode.getD (table.get i))) [] [] (table.get i :: output)) (2 * (i.val + 1)) := by
  have hsplit : table.take i.val ++ table.get i :: table.drop (i.val + 1) = table := by
    rw [List.get_eq_getElem, List.getElem_cons_drop i.isLt, List.take_append_drop]
  have hn : (table.take i.val).length = i.val := by simp
  have hs : table.set i.val (mode.getD (table.get i)) =
      table.take i.val ++ mode.getD (table.get i) :: table.drop (i.val + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos i.isLt]
  simpa only [hsplit, hn, ← hs] using access_exact mode (table.take i.val) (table.get i) (table.drop (i.val + 1)) output

theorem program_budget (mode : Option Bool) (label : Fin 4) : TM2Cost.budget ((machine mode).program label) ≤ 8 := by
  fin_cases label <;> simp [machine, scanStmt, TM2Cost.budget, copyMoveStmt]

/-- Arbitrary oversized or malformed indexes terminate in physical table length.
Even the rejection case cannot loop once the actual data stack is exhausted. -/
theorem total (mode : Option Bool) (table index scratch output : List Bool) :
    ∃ (last : (machine mode).Config) (time : ℕ),
      time ≤ 2 * table.length + scratch.length + 2 ∧ (last.l = some 2 ∨ last.l = some 3) ∧
      RunsExactly (machine mode).computer.step (config 0 table index scratch output) last time := by
  induction table generalizing index scratch with
  | nil =>
    exact ⟨config 3 [] index.tail scratch output, 1, by simp, Or.inr rfl,
      runsExactly_one (scan_missing mode index scratch output)⟩
  | cons bit table ih =>
    cases index with
    | nil =>
      refine ⟨config 2 (scratch.reverse ++ mode.getD bit :: table) [] [] (bit :: output),
        scratch.length + 1 + 1, by simp, Or.inl rfl, ?_⟩
      exact (runsExactly_one (scan_select mode bit table scratch output)).trans
        (restore_exact mode (mode.getD bit :: table) scratch (bit :: output))
    | cons token index =>
      obtain ⟨last, time, ht, hl, hr⟩ := ih index (bit :: scratch)
      exact ⟨last, time + 1, by simp only [List.length_cons] at *; omega, hl,
        (runsExactly_one (scan_cons mode bit token table index scratch output)).trans hr⟩

/-- The independent primitive interpreter charges every bit and restoration operation. -/
theorem bit_cost (mode : Option Bool) (table : List Bool) (i : Fin table.length) (output : List Bool) :
    (Primitive.run (machine mode).program (2 * (i.val + 1))
      (some (config 0 table (List.replicate i.val true) [] output))).2 =
      some (config 2 (table.set i.val (mode.getD (table.get i))) [] [] (table.get i :: output)) ∧
    (Primitive.run (machine mode).program (2 * (i.val + 1))
      (some (config 0 table (List.replicate i.val true) [] output))).1 ≤ 16 * (table.length + 1) := by
  have h := Primitive.execution_cost (machine mode).program 8 (program_budget mode) _ _ _ (get_exact mode table i output)
  refine ⟨h.1, le_trans h.2 ?_⟩
  have hi := i.isLt
  omega

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.BitTable
