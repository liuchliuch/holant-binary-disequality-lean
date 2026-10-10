import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.GraphPreprocessing.WordEqual
import Mathlib.Tactic.Linarith

/-!
# Literal framed-record search by a finite Boolean-stack machine

Each candidate is really unframed, the query is really copied and restored, both
words are compared bit by bit, and a physical unary occurrence index is allocated.
The query and every original record bit are ordinary Boolean stack data. Equality
of unbounded words and list search appear only in the specification, never in a
finite-control callback. This supplies search within an original vertex's ports.
-/
namespace Holant.Complexity.GraphPreprocessing.FramedFind
open Turing Computability StackProtocol
open Turing.TM2.Stmt

abbrev Caller := Bool × Option Bool × Unit

def markerStmt : Stmt (Fin 7) (Fin 10) Caller :=
  pop 0 (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (load (fun v => (none, v.2)) (goto (fun _ => 1)))
        (load (fun v => (none, v.2)) (goto (fun _ => 8))))
      (load (fun v => (none, v.2)) (goto (fun _ => 9))))

abbrev machine : BinaryCompose.Machine where
  K := Fin 7
  input := 0
  output := 6
  Label := Fin 10
  main := 0
  State := WordEqual.Memory Unit
  initial := WordEqual.clean true ()
  program label := if label = 0 then markerStmt
    else if label = 1 then Frame.scanStmt 0 4 1 2 9
    else if label = 2 then copyMoveStmt 4 2 2 3
    else if label = 3 then copyMoveStmt 1 5 3 4
    else if label = 4 then copyRestoreStmt 1 3 5 4 5
    else if label = 5 then WordEqual.statement 2 3 5 6 7
    else if label = 7 then push 6 (fun _ => true)
      (load (fun _ => WordEqual.clean true ()) (goto (fun _ => 0)))
    else .halt

def tapes (source query payload comparison parseTmp copyTmp counter : List Bool) : Fin 7 → List Bool :=
  ![source, query, payload, comparison, parseTmp, copyTmp, counter]

def config (label : Fin 10) (same : Bool)
    (source query payload comparison parseTmp copyTmp counter : List Bool) : machine.Config :=
  WordEqual.cfg label same () (tapes source query payload comparison parseTmp copyTmp counter)

private theorem scan_exec : ExecutesAt machine.computer.step (1 : Fin 10) (Frame.scanStmt 0 4 1 2 9) := by intro state tapes; rfl
private theorem restore_exec : ExecutesAt machine.computer.step (2 : Fin 10) (copyMoveStmt 4 2 2 3) := by intro state tapes; rfl
private theorem copy_move_exec : ExecutesAt machine.computer.step (3 : Fin 10) (copyMoveStmt 1 5 3 4) := by intro state tapes; rfl
private theorem copy_restore_exec : ExecutesAt machine.computer.step (4 : Fin 10) (copyRestoreStmt 1 3 5 4 5) := by intro state tapes; rfl
private theorem compare_exec : WordEqual.ExecutesAt machine.computer.step (5 : Fin 10) (WordEqual.statement 2 3 5 6 7) := by intro state tapes; rfl

theorem marker_entry (source query counter : List Bool) :
    machine.computer.step (config 0 true (true :: source) query [] [] [] [] counter) =
      some (config 1 true source query [] [] [] [] counter) := by
  simp [FinTM2.step, TM2.step, machine, config, WordEqual.cfg, WordEqual.clean, markerStmt, TM2.stepAux, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem marker_end (source query counter : List Bool) :
    machine.computer.step (config 0 true (false :: source) query [] [] [] [] counter) =
      some (config 8 true source query [] [] [] [] counter) := by
  simp [FinTM2.step, TM2.step, machine, config, WordEqual.cfg, WordEqual.clean, markerStmt, TM2.stepAux, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem advance (source query counter : List Bool) :
    machine.computer.step (config 7 false source query [] [] [] [] counter) =
      some (config 0 true source query [] [] [] [] (true :: counter)) := by
  simp [FinTM2.step, TM2.step, machine, config, WordEqual.cfg, WordEqual.clean, TM2.stepAux, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem extract (word source query counter : List Bool) :
    RunsExactly machine.computer.step
      (config 1 true (Holant.Algebraic.frame word ++ source) query [] [] [] [] counter)
      (config 3 true source query word [] [] [] counter) (2 * (word.length + 1)) := by
  have h := Frame.extract_exact (0 : Fin 7) 2 4 (by decide) (by decide) (by decide)
    machine.computer.step 1 2 3 9 scan_exec restore_exec (true, none, ())
      (tapes [] query [] [] [] [] counter) word source []
  simp only [List.append_nil] at h
  convert h using 1 <;> unfold config WordEqual.cfg cfg WordEqual.clean <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem copy_query (source query word counter : List Bool) :
    RunsExactly machine.computer.step (config 3 true source query word [] [] [] counter)
      (config 5 true source query word query [] [] counter) (2 * (query.length + 1)) := by
  have h := copy_exact (1 : Fin 7) 3 5 (by decide) (by decide) (by decide)
    machine.computer.step 3 4 5 copy_move_exec copy_restore_exec (true, none, ())
      (tapes source query word [] [] [] counter) rfl
  change RunsExactly _ _ (cfg _ _ (Function.update _ 3 (query ++ []))) _ at h
  simp only [List.append_nil] at h
  convert h using 1
  · rfl
  · unfold config WordEqual.cfg cfg WordEqual.clean
    congr 1
    funext k
    fin_cases k <;> rfl
  · rfl

theorem compare_words (source query word counter : List Bool) :
    RunsExactly machine.computer.step (config 5 true source query word query [] [] counter)
      (config (if word = query then 6 else 7) (decide (word = query)) source query [] [] [] [] counter)
      (max word.length query.length + 1) := by
  have h := WordEqual.compare_exact (2 : Fin 7) 3 (by decide) machine.computer.step 5 6 7
    compare_exec true () (tapes source query [] [] [] [] counter) word query
  simp only [Bool.true_and, Bool.decide_iff] at h
  change RunsExactly _ _ _ _ at h
  convert h using 1 <;> unfold config WordEqual.cfg <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

def inspectTicks (word query : List Bool) : ℕ :=
  2 * word.length + 2 * query.length + max word.length query.length + 6

/-- One complete record comparison really executes parsing, copying and equality. -/
theorem inspect_exact (word source query counter : List Bool) :
    RunsExactly machine.computer.step
      (config 0 true (true :: (Holant.Algebraic.frame word ++ source)) query [] [] [] [] counter)
      (config (if word = query then 6 else 7) (decide (word = query)) source query [] [] [] [] counter)
      (inspectTicks word query) := by
  have h := (((runsExactly_one (marker_entry (Holant.Algebraic.frame word ++ source) query counter)).trans
    (extract word source query counter)).trans (copy_query source query word counter)).trans
    (compare_words source query word counter)
  convert h using 1
  unfold inspectTicks
  omega

def ticks {α : Type} (e : Encoding α Bool) (query : α) (pre : List α) : ℕ :=
  (pre.map (fun a => inspectTicks (e.encode a) (e.encode query) + 1)).sum + 5 * (e.encode query).length + 6

/-- Exact first matching original record, including its unary original position. -/
theorem find_exact {α : Type} (e : Encoding α Bool) (query : α) (pre tail : List α)
    (hpre : ∀ a ∈ pre, a ≠ query) (suffix counter : List Bool) :
    RunsExactly machine.computer.step
      (config 0 true (framedListEncode e (pre ++ query :: tail) ++ suffix) (e.encode query) [] [] [] [] counter)
      (config 6 true (framedListEncode e tail ++ suffix) (e.encode query) [] [] [] []
        (List.replicate pre.length true ++ counter)) (ticks e query pre) := by
  induction pre generalizing counter with
  | nil =>
    have h := inspect_exact (e.encode query) (framedListEncode e tail ++ suffix) (e.encode query) counter
    have ht : inspectTicks (e.encode query) (e.encode query) = 5 * (e.encode query).length + 6 := by
      unfold inspectTicks
      rw [max_self]
      omega
    rw [ht] at h
    simpa [framedListEncode, ticks, List.append_assoc] using h
  | cons a pre ih =>
    have ha : e.encode a ≠ e.encode query := fun h => hpre a (by simp) (e.encode_injective h)
    have first := inspect_exact (e.encode a) (framedListEncode e (pre ++ query :: tail) ++ suffix) (e.encode query) counter
    simp only [ha, ↓reduceIte, decide_false] at first
    have next := runsExactly_one (advance (framedListEncode e (pre ++ query :: tail) ++ suffix) (e.encode query) counter)
    have rest := ih (fun x hx => hpre x (by simp [hx])) (true :: counter)
    have run := (first.trans next).trans rest
    convert run using 1
    · simp [framedListEncode, List.append_assoc]
    · congr 1
      rw [List.length_cons, List.replicate_add]
      simp [List.append_assoc]
    · simp only [ticks, List.map_cons, List.sum_cons]
      omega

/-- Exhausting a list with no matching record returns the distinct missing label. -/
theorem missing_exact {α : Type} (e : Encoding α Bool) (query : α) (xs : List α)
    (hx : ∀ a ∈ xs, a ≠ query) (suffix counter : List Bool) :
    RunsExactly machine.computer.step
      (config 0 true (framedListEncode e xs ++ suffix) (e.encode query) [] [] [] [] counter)
      (config 8 true suffix (e.encode query) [] [] [] [] (List.replicate xs.length true ++ counter))
      ((xs.map (fun a => inspectTicks (e.encode a) (e.encode query) + 1)).sum + 1) := by
  induction xs generalizing counter with
  | nil => simpa [framedListEncode] using runsExactly_one (marker_end suffix (e.encode query) counter)
  | cons a xs ih =>
    have ha : e.encode a ≠ e.encode query := fun h => hx a (by simp) (e.encode_injective h)
    have first := inspect_exact (e.encode a) (framedListEncode e xs ++ suffix) (e.encode query) counter
    simp only [ha, ↓reduceIte, decide_false] at first
    have next := runsExactly_one (advance (framedListEncode e xs ++ suffix) (e.encode query) counter)
    have rest := ih (fun x h => hx x (by simp [h])) (true :: counter)
    have run := (first.trans next).trans rest
    convert run using 1
    · simp [framedListEncode, List.append_assoc]
    · congr 1
      rw [List.length_cons, List.replicate_add]
      simp [List.append_assoc]
    · simp only [List.map_cons, List.sum_cons]
      omega

/-- Query-copy overhead is charged once for every actual scanned record. -/
theorem ticks_le_bits {α : Type} (e : Encoding α Bool) (query : α) (pre tail : List α) :
    ticks e query pre ≤ 8 * ((framedListEncode e (pre ++ query :: tail)).length + 1) * ((e.encode query).length + 1) := by
  induction pre with
  | nil =>
    simp only [ticks, List.map_nil, List.sum_nil, Nat.zero_add, List.nil_append, framedListEncode,
      List.length_cons, List.length_append, Holant.Algebraic.frame_length]
    nlinarith
  | cons a pre ih =>
    simp only [ticks, List.map_cons, List.sum_cons, List.cons_append, framedListEncode,
      List.length_cons, List.length_append, Holant.Algebraic.frame_length] at *
    have hm : max (e.encode a).length (e.encode query).length ≤ (e.encode a).length + (e.encode query).length := by omega
    simp only [inspectTicks] at *
    nlinarith

theorem program_budget (label : Fin 10) : TM2Cost.budget (machine.program label) ≤ 8 := by
  fin_cases label <;> decide

/-- Actual primitive interpreter count for the exact found-record run. -/
theorem find_bit_cost {α : Type} (e : Encoding α Bool) (query : α) (pre tail : List α)
    (suffix counter : List Bool) :
    (Primitive.run machine.program (ticks e query pre)
      (some (config 0 true (framedListEncode e (pre ++ query :: tail) ++ suffix) (e.encode query) [] [] [] [] counter))).1 ≤
      64 * ((framedListEncode e (pre ++ query :: tail)).length + 1) * ((e.encode query).length + 1) := by
  have h := Primitive.run_cost_le machine.program 8 program_budget (ticks e query pre)
    (some (config 0 true (framedListEncode e (pre ++ query :: tail) ++ suffix) (e.encode query) [] [] [] [] counter))
  have h' := Nat.mul_le_mul_left 8 (ticks_le_bits e query pre tail)
  exact le_trans h (by simpa only [← Nat.mul_assoc] using h')

end Holant.Complexity.GraphPreprocessing.FramedFind
