import Holant.Complexity.StackProtocol
import Holant.Complexity.FramedEncoding

/-!
# Returning framed-word parsing on actual Boolean stacks

The parser distinguishes EOF, a false terminator, and a truncated true/payload
pair. Its optional-bit register and all callbacks are finite. Every payload bit
is popped and pushed by the displayed TM2 program. The proved result retains the
unconsumed input suffix, arbitrary caller memory, and every unrelated stack.
-/

namespace Holant.Complexity.GraphPreprocessing.Frame

open Turing Holant.Algebraic StackProtocol
open Turing.TM2.Stmt

variable {K Λ τ : Type} [DecidableEq K]

/-- Decode one framing pair per transition. EOF and a dangling true marker reject. -/
def scanStmt (src tmp : K) (loop good bad : Λ) : Stmt K Λ τ :=
  pop src (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (pop src (fun v b => (b, v.2))
          (branch (fun v => v.1.isSome)
            (push tmp (fun v => v.1.getD false)
              (load (fun v => (none, v.2)) (goto (fun _ => loop))))
            (load (fun v => (none, v.2)) (goto (fun _ => bad)))))
        (load (fun v => (none, v.2)) (goto (fun _ => good))))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

omit [DecidableEq K] in
@[simp] theorem scanStmt_budget (src tmp : K) (loop good bad : Λ) :
    TM2Cost.budget (scanStmt (τ := τ) src tmp loop good bad) = 8 := rfl

section Execution

variable (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop good bad : Λ)
variable (hs : ExecutesAt step loop (scanStmt src tmp loop good bad))
include hs

include hsd hst in
theorem step_pair (memory : τ) (frame : K → List Bool)
    (bit : Bool) (input output scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp (true :: bit :: input) output scratch)) =
      some (cfg loop memory (tapes3 frame src dst tmp input output (bit :: scratch))) := by
  rw [cfg, hs]
  simp [scanStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hsd hst in
theorem step_terminator (memory : τ) (frame : K → List Bool)
    (input output scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp (false :: input) output scratch)) =
      some (cfg good memory (tapes3 frame src dst tmp input output scratch)) := by
  rw [cfg, hs]
  simp [scanStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hsd hst in
theorem step_eof (memory : τ) (frame : K → List Bool) (output scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp [] output scratch)) =
      some (cfg bad memory (tapes3 frame src dst tmp [] output scratch)) := by
  rw [cfg, hs]
  simp [scanStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hsd hst in
theorem step_truncated (memory : τ) (frame : K → List Bool) (output scratch : List Bool) :
    step (cfg loop memory (tapes3 frame src dst tmp [true] output scratch)) =
      some (cfg bad memory (tapes3 frame src dst tmp [] output scratch)) := by
  rw [cfg, hs]
  simp [scanStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hsd hst in
/-- Exact real execution of framing removal, including the terminator transition. -/
theorem scan_exact (memory : τ) (frame : K → List Bool)
    (word suffix output scratch : List Bool) :
    RunsExactly step
      (cfg loop memory (tapes3 frame src dst tmp (Holant.Algebraic.frame word ++ suffix) output scratch))
      (cfg good memory (tapes3 frame src dst tmp suffix output (word.reverse ++ scratch)))
      (word.length + 1) := by
  induction word generalizing scratch with
  | nil => simpa [Holant.Algebraic.frame] using (runsExactly_one
      (step_terminator src dst tmp hsd hst step loop good bad hs memory frame suffix output scratch))
  | cons bit word ih =>
    have run := (runsExactly_one (step_pair src dst tmp hsd hst step loop good bad hs
      memory frame bit (Holant.Algebraic.frame word ++ suffix) output scratch)).trans (ih (bit :: scratch))
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using run

include hsd hst in
/-- Every malformed frame rejects in at most input length plus one transitions.
No natural-valued identifier is decoded or used as a loop bound. -/
theorem rejects (memory : τ) (frame : K → List Bool)
    (input output scratch : List Bool) (h : unframe input = none) :
    ∃ (produced : List Bool) (time : ℕ), time ≤ input.length + 1 ∧ produced.length ≤ input.length ∧
      RunsExactly step (cfg loop memory (tapes3 frame src dst tmp input output scratch))
        (cfg bad memory (tapes3 frame src dst tmp [] output (produced.reverse ++ scratch))) time := by
  induction input using unframe.induct generalizing scratch with
  | case1 =>
    exact ⟨[], 1, by simp, by simp, by simpa using (runsExactly_one
      (step_eof src dst tmp hsd hst step loop good bad hs memory frame output scratch))⟩
  | case2 rest => simp [unframe] at h
  | case3 =>
    exact ⟨[], 1, by simp, by simp, by simpa using (runsExactly_one
      (step_truncated src dst tmp hsd hst step loop good bad hs memory frame output scratch))⟩
  | case4 bit rest ih =>
    have hn : unframe rest = none := by simpa [unframe] using h
    obtain ⟨produced, time, ht, hp, hr⟩ := ih (bit :: scratch) hn
    refine ⟨bit :: produced, time + 1, by simp only [List.length_cons]; omega,
      by simp only [List.length_cons]; omega, ?_⟩
    have run := (runsExactly_one (step_pair src dst tmp hsd hst step loop good bad hs
      memory frame bit rest output scratch)).trans hr
    simpa [List.reverse_cons, List.append_assoc] using run

end Execution

/-- The existing decoder accepts exactly a framed prefix and its remaining suffix. -/
theorem unframe_some_iff (input word suffix : List Bool) :
    unframe input = some (word, suffix) ↔ input = Holant.Algebraic.frame word ++ suffix := by
  constructor
  · intro h
    induction input using unframe.induct generalizing word with
    | case1 => simp [unframe] at h
    | case2 rest =>
      have hp : ([], rest) = (word, suffix) := Option.some.inj h
      cases hp
      rfl
    | case3 => simp [unframe] at h
    | case4 bit rest ih =>
      cases hu : unframe rest with
      | none => simp [unframe, hu] at h
      | some p =>
        have hp : (bit :: p.1, p.2) = (word, suffix) := by simpa [unframe, hu] using h
        cases hp
        rw [ih p.1 hu]
        rfl
  · rintro rfl
    exact unframe_frame_append word suffix

section Restore

variable (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (restore next : Λ)
variable (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
include hr

include hdt in
theorem restore_step (memory : τ) (frame : K → List Bool)
    (bit : Bool) (input output scratch : List Bool) :
    step (cfg restore memory (tapes3 frame src dst tmp input output (bit :: scratch))) =
      some (cfg restore memory (tapes3 frame src dst tmp input (bit :: output) scratch)) := by
  rw [cfg, hr]
  simp [copyMoveStmt, TM2.stepAux, cfg, tapes3_dst src dst tmp hdt,
    update_tapes3_dst src dst tmp hdt]

theorem restore_nil (memory : τ) (frame : K → List Bool) (input output : List Bool) :
    step (cfg restore memory (tapes3 frame src dst tmp input output [])) =
      some (cfg next memory (tapes3 frame src dst tmp input output [])) := by
  rw [cfg, hr]
  simp [copyMoveStmt, TM2.stepAux, cfg]

include hdt in
theorem restore_exact (memory : τ) (frame : K → List Bool)
    (input output scratch : List Bool) :
    RunsExactly step (cfg restore memory (tapes3 frame src dst tmp input output scratch))
      (cfg next memory (tapes3 frame src dst tmp input (scratch.reverse ++ output) []))
      (scratch.length + 1) := by
  induction scratch generalizing output with
  | nil => simpa using runsExactly_one (restore_nil src dst tmp step restore next hr memory frame input output)
  | cons bit scratch ih =>
    have run := (runsExactly_one (restore_step src dst tmp hdt step restore next hr
      memory frame bit input output scratch)).trans (ih (bit :: output))
    simpa [List.reverse_cons, List.append_assoc] using run

end Restore

/-- Ordered extraction is two proved bit-stack loops; no whole-word copy opcode. -/
theorem extract_exact (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (scan restore next bad : Λ)
    (hs : ExecutesAt step scan (scanStmt src tmp scan restore bad))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (frame : K → List Bool) (word suffix output : List Bool) :
    RunsExactly step
      (cfg scan memory (tapes3 frame src dst tmp (Holant.Algebraic.frame word ++ suffix) output []))
      (cfg next memory (tapes3 frame src dst tmp suffix (word ++ output) []))
      (2 * (word.length + 1)) := by
  have first := scan_exact src dst tmp hsd hst step scan restore bad hs memory frame word suffix output []
  simp only [List.append_nil] at first
  have second := restore_exact src dst tmp hdt step restore next hr memory frame suffix output word.reverse
  simpa [Nat.two_mul] using first.trans second

/-- A returning timed contract, preserving the actual input suffix and caller frame. -/
def extract_correct (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (scan restore next bad : Λ)
    (hs : ExecutesAt step scan (scanStmt src tmp scan restore bad))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (frame : K → List Bool) (word suffix output : List Bool) :
    StateTransition.EvalsToInTime step
      (cfg scan memory (tapes3 frame src dst tmp (Holant.Algebraic.frame word ++ suffix) output []))
      (some (cfg next memory (tapes3 frame src dst tmp suffix (word ++ output) [])))
      (2 * (word.length + 1)) :=
  (extract_exact src dst tmp hsd hst hdt step scan restore next bad hs hr memory frame word suffix output).toTimed

end Holant.Complexity.GraphPreprocessing.Frame
