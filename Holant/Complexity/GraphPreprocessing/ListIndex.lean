import Holant.Complexity.GraphPreprocessing.FrameMachine
import Holant.Complexity.GraphPreprocessing.ListScan
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# Bounded-index framed-list access by an actual Boolean-stack machine

The index is a unary stack, suitable for the physically bounded graph counters.
One index bit is consumed only after an actual list entry marker. Skipping a
record and extracting the selected record are proved bit-stack loops. All loops
inspect bits and EOF, with no whole-list search or numeric-index callback.
-/
namespace Holant.Complexity.GraphPreprocessing.ListIndex
open Turing StackProtocol Computability
open Turing.TM2.Stmt

/-- The index emptiness test is an ordinary stack pop, not a host natural test. -/
def seekStmt : Stmt (Fin 4) (Fin 7) Unit :=
  pop 0 (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (pop 1 (fun v bit => (bit, v.2))
          (branch (fun v => v.1.isSome)
            (load (fun v => (none, v.2)) (goto (fun _ => 1)))
            (load (fun v => (none, v.2)) (goto (fun _ => 2)))))
        (load (fun v => (none, v.2)) (goto (fun _ => 5))))
      (load (fun v => (none, v.2)) (goto (fun _ => 6))))

abbrev machine : BinaryCompose.Machine where
  K := Fin 4
  input := 0
  output := 2
  Label := Fin 7
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then seekStmt
    else if label = 1 then ListScan.skipStmt 0 1 0 6
    else if label = 2 then Frame.scanStmt 0 3 2 3 6
    else if label = 3 then copyMoveStmt 3 2 3 4 else .halt

def tapes (input index output scratch : List Bool) : Fin 4 → List Bool := ![input, index, output, scratch]

private theorem skip_exec : ExecutesAt machine.computer.step (1 : Fin 7) (ListScan.skipStmt 0 1 0 6) := by
  intro state tapes; rfl
private theorem scan_exec : ExecutesAt machine.computer.step (2 : Fin 7) (Frame.scanStmt 0 3 2 3 6) := by
  intro state tapes; rfl
private theorem restore_exec : ExecutesAt machine.computer.step (3 : Fin 7) (copyMoveStmt 3 2 3 4) := by
  intro state tapes; rfl

theorem seek_cons (input index output scratch : List Bool) (bit : Bool) :
    machine.computer.step (cfg (0 : Fin 7) () (tapes (true :: input) (bit :: index) output scratch)) =
      some (cfg (1 : Fin 7) () (tapes input index output scratch)) := by
  dsimp [FinTM2.step, TM2.step, machine, seekStmt, cfg, tapes, TM2.stepAux]
  simp only [Bool.cond_true, Bool.cond_false, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
  dsimp
  simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem seek_zero (input output scratch : List Bool) :
    machine.computer.step (cfg (0 : Fin 7) () (tapes (true :: input) [] output scratch)) =
      some (cfg (2 : Fin 7) () (tapes input [] output scratch)) := by
  dsimp [FinTM2.step, TM2.step, machine, seekStmt, cfg, tapes, TM2.stepAux]
  simp only [Bool.cond_true, Bool.cond_false, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
  dsimp
  simp only [Bool.cond_true, Bool.cond_false]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem seek_missing (input index output scratch : List Bool) :
    machine.computer.step (cfg (0 : Fin 7) () (tapes (false :: input) index output scratch)) =
      some (cfg (5 : Fin 7) () (tapes input index output scratch)) := by
  dsimp [FinTM2.step, TM2.step, machine, seekStmt, cfg, tapes, TM2.stepAux]
  simp only [Bool.cond_true, Bool.cond_false, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem seek_eof (index output scratch : List Bool) :
    machine.computer.step (cfg (0 : Fin 7) () (tapes [] index output scratch)) =
      some (cfg (6 : Fin 7) () (tapes [] index output scratch)) := by
  dsimp [FinTM2.step, TM2.step, machine, seekStmt, cfg, tapes, TM2.stepAux]
  simp only [Bool.cond_true, Bool.cond_false, Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem skip_exact (word suffix index output scratch : List Bool) :
    RunsExactly machine.computer.step
      (cfg (1 : Fin 7) () (tapes (Holant.Algebraic.frame word ++ suffix) index output scratch))
      (cfg (0 : Fin 7) () (tapes suffix index output scratch)) (word.length + 1) := by
  have h := ListScan.skip_exact (0 : Fin 4) 1 (by decide) machine.computer.step 1 0 6 skip_exec ()
    (tapes [] [] output scratch) word suffix index
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem extract_exact (word suffix output : List Bool) :
    RunsExactly machine.computer.step
      (cfg (2 : Fin 7) () (tapes (Holant.Algebraic.frame word ++ suffix) [] output []))
      (cfg (4 : Fin 7) () (tapes suffix [] (word ++ output) [])) (2 * (word.length + 1)) := by
  have h := Frame.extract_exact (0 : Fin 4) 2 3 (by decide) (by decide) (by decide)
    machine.computer.step 2 3 4 6 scan_exec restore_exec () (fun _ => []) word suffix output
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

/-- Exact transition count through an existing pre and the selected record. -/
def ticks {α : Type} (e : Encoding α Bool) (pre : List α) (selected : α) : ℕ :=
  (pre.map (fun a => (e.encode a).length + 2)).sum + 2 * ((e.encode selected).length + 1) + 1

/-- Real indexed extraction retains the remaining list serialization verbatim. -/
theorem index_exact {α : Type} (e : Encoding α Bool) (pre tail : List α) (selected : α)
    (suffix output : List Bool) :
    RunsExactly machine.computer.step
      (cfg (0 : Fin 7) () (tapes (framedListEncode e (pre ++ selected :: tail) ++ suffix)
        (List.replicate pre.length true) output []))
      (cfg (4 : Fin 7) () (tapes (framedListEncode e tail ++ suffix) [] (e.encode selected ++ output) []))
      (ticks e pre selected) := by
  induction pre with
  | nil =>
    have h := (runsExactly_one (seek_zero
      (Holant.Algebraic.frame (e.encode selected) ++ framedListEncode e tail ++ suffix) output [])).trans
      (by simpa only [List.append_assoc] using extract_exact (e.encode selected) (framedListEncode e tail ++ suffix) output)
    simpa [ticks, framedListEncode, List.append_assoc] using h
  | cons a pre ih =>
    have first := runsExactly_one (seek_cons
      (Holant.Algebraic.frame (e.encode a) ++ framedListEncode e (pre ++ selected :: tail) ++ suffix)
      (List.replicate pre.length true) output [] true)
    have second := skip_exact (e.encode a) (framedListEncode e (pre ++ selected :: tail) ++ suffix)
      (List.replicate pre.length true) output []
    have run := (first.trans (by simpa only [List.append_assoc] using second)).trans ih
    convert run using 1
    · simp [framedListEncode, List.append_assoc, List.replicate_succ]
    · simp only [ticks, List.map_cons, List.sum_cons]; omega

theorem ticks_le_bits {α : Type} (e : Encoding α Bool) (pre tail : List α) (selected : α) :
    ticks e pre selected ≤ (framedListEncode e (pre ++ selected :: tail)).length + 1 := by
  induction pre with
  | nil =>
    simp only [ticks, List.map_nil, List.sum_nil, List.nil_append, Nat.zero_add,
      framedListEncode, List.length_cons, List.length_append, Holant.Algebraic.frame_length]
    omega
  | cons a pre ih =>
    simp only [ticks, List.map_cons, List.sum_cons, List.cons_append, framedListEncode,
      List.length_cons, List.length_append, Holant.Algebraic.frame_length] at *
    omega

theorem program_budget (label : Fin 7) : TM2Cost.budget (machine.program label) ≤ 8 := by
  fin_cases label <;> decide

/-- All the actual elementary Boolean instructions for access are linearly bounded. -/
theorem index_bit_cost {α : Type} (e : Encoding α Bool) (pre tail : List α) (selected : α)
    (suffix output : List Bool) :
    (Primitive.run machine.program (ticks e pre selected)
      (some (cfg (0 : Fin 7) () (tapes (framedListEncode e (pre ++ selected :: tail) ++ suffix)
        (List.replicate pre.length true) output [])))).1 ≤
      8 * ((framedListEncode e (pre ++ selected :: tail)).length + 1) := by
  exact le_trans (Primitive.run_cost_le machine.program 8 program_budget _ _) (Nat.mul_le_mul_left 8 (ticks_le_bits e pre tail selected))

end Holant.Complexity.GraphPreprocessing.ListIndex
