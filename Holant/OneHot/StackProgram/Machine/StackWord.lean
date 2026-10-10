import Holant.OneHot.StackProgram.Machine.Dispatch
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-! Returning extraction and insertion of one value in the established framed
stack-list codec. All delimiter, marker, reversal, EOF-test and scratch-reset
transitions are included. Only Boolean symbols enter finite control memory. -/
namespace Holant.OneHot.StackProgram.Machine.StackWord
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt
variable {K Λ τ : Type} [DecidableEq K]

/-- The false list marker means underflow, whereas EOF means malformed input. -/
def markerStmt (src : K) (scan missing bad : Λ) : Stmt K Λ τ :=
  pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
    (branch (fun v => v.1.getD false)
      (load (fun v => (none, v.2)) (goto (fun _ => scan)))
      (load (fun v => (none, v.2)) (goto (fun _ => missing))))
    (load (fun v => (none, v.2)) (goto (fun _ => bad))))

def consStmt (dst : K) (next : Λ) : Stmt K Λ τ := push dst (fun _ => true) (goto (fun _ => next))

section Pop
variable (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (entry scan restore good missing bad : Λ)
variable (hm : ExecutesAt step entry (markerStmt src scan missing bad))
variable (hs : ExecutesAt step scan (GraphPreprocessing.Frame.scanStmt src tmp scan restore bad))
variable (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore good))
include hsd hst hm

theorem marker_cons (memory : τ) (frame : K → List Bool) (input output scratch : List Bool) :
    step (cfg entry memory (tapes3 frame src dst tmp (true :: input) output scratch)) =
      some (cfg scan memory (tapes3 frame src dst tmp input output scratch)) := by
  rw [cfg, hm]
  simp [markerStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

theorem marker_missing (memory : τ) (frame : K → List Bool) (suffix output scratch : List Bool) :
    step (cfg entry memory (tapes3 frame src dst tmp (false :: suffix) output scratch)) =
      some (cfg missing memory (tapes3 frame src dst tmp suffix output scratch)) := by
  rw [cfg, hm]
  simp [markerStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

theorem marker_eof (memory : τ) (frame : K → List Bool) (output scratch : List Bool) :
    step (cfg entry memory (tapes3 frame src dst tmp [] output scratch)) =
      some (cfg bad memory (tapes3 frame src dst tmp [] output scratch)) := by
  rw [cfg, hm]
  simp [markerStmt, TM2.stepAux, cfg, tapes3_src src dst tmp hsd hst,
    update_tapes3_src src dst tmp hsd hst]

include hdt hs hr in
/-- Extract exactly one stack element, preserving its entire encoded suffix. -/
theorem pop_exact (memory : τ) (frame : K → List Bool) (word suffix output : List Bool) :
    RunsExactly step
      (cfg entry memory (tapes3 frame src dst tmp
        (true :: Holant.Algebraic.frame word ++ suffix) output []))
      (cfg good memory (tapes3 frame src dst tmp suffix (word ++ output) []))
      (2 * word.length + 3) := by
  have first := runsExactly_one (marker_cons src dst tmp hsd hst step entry scan missing bad hm
    memory frame (Holant.Algebraic.frame word ++ suffix) output [])
  have second := GraphPreprocessing.Frame.extract_exact src dst tmp hsd hst hdt step
    scan restore good bad hs hr memory frame word suffix output
  convert first.trans second using 1
  simp only [List.cons_append]
end Pop

/-- Insert a raw word as one stack element and clean both temporary stacks. -/
theorem push_exact (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (move delimiter emit marker good : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move delimiter))
    (hd : ExecutesAt step delimiter (FixedFieldMachines.FrameEmit.delimiterStmt dst emit))
    (he : ExecutesAt step emit (FixedFieldMachines.FrameEmit.emitStmt tmp dst emit marker))
    (hk : ExecutesAt step marker (consStmt dst good))
    (memory : τ) (frame : K → List Bool) (word suffix : List Bool) :
    RunsExactly step (cfg move memory (tapes3 frame src dst tmp word suffix []))
      (cfg good memory (tapes3 frame src dst tmp []
        (true :: Holant.Algebraic.frame word ++ suffix) [])) (2 * word.length + 4) := by
  have first := FixedFieldMachines.FrameEmit.prepend_exact src dst tmp hsd hst hdt step
    move delimiter emit marker hm hd he memory frame word suffix
  have last : step (cfg marker memory (tapes3 frame src dst tmp [] (Holant.Algebraic.frame word ++ suffix) [])) =
      some (cfg good memory (tapes3 frame src dst tmp []
        (true :: Holant.Algebraic.frame word ++ suffix) [])) := by
    rw [cfg, hk]
    simp [consStmt, TM2.stepAux, cfg, tapes3_dst src dst tmp hdt,
      update_tapes3_dst src dst tmp hdt]
  convert first.trans (runsExactly_one last) using 1
  omega

/-- Order-preserving destructive transfer with an arbitrary retained caller frame. -/
theorem move_exact (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (move restore good : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore good))
    (memory : τ) (frame : K → List Bool) (word suffix : List Bool) :
    RunsExactly step (cfg move memory (tapes3 frame src dst tmp word suffix []))
      (cfg good memory (tapes3 frame src dst tmp [] (word ++ suffix) []))
      (2 * (word.length + 1)) := by
  have first := copy_move_exact src dst tmp hsd hst step move restore hm memory frame word suffix []
  have last := GraphPreprocessing.Frame.restore_exact src dst tmp hdt step restore good hr
    memory frame [] suffix word.reverse
  simp only [List.append_nil] at first
  simpa [Nat.two_mul] using first.trans last

/-- One real finite Boolean machine exposes both returning entry points. -/
abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 10
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then markerStmt 0 1 4 5
    else if label = 1 then GraphPreprocessing.Frame.scanStmt 0 2 1 2 5
    else if label = 2 then copyMoveStmt 2 1 2 3
    else if label = 6 then copyMoveStmt 1 2 6 7
    else if label = 7 then FixedFieldMachines.FrameEmit.delimiterStmt 0 8
    else if label = 8 then FixedFieldMachines.FrameEmit.emitStmt 2 0 8 9
    else if label = 9 then consStmt 0 3
    else .halt

/-- Correct against the exact previously established fieldword-stack codec. -/
theorem machine_pop {V : Type} (e : Encoding V Bool) (x : V) (s : List V) :
    RunsExactly machine.computer.step
      (cfg (0 : Fin 10) () (GraphPreprocessing.Frame.tapes ((stackEncoding e).encode (x :: s)) [] []))
      (cfg (3 : Fin 10) () (GraphPreprocessing.Frame.tapes ((stackEncoding e).encode s) (e.encode x) []))
      (2 * (e.encode x).length + 3) := by
  have h := pop_exact (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    machine.computer.step 0 1 2 3 4 5
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) (e.encode x) ((stackEncoding e).encode s) []
  simpa [← GraphPreprocessing.Frame.tapes_eq, stackEncoding, framedListEncoding, framedListEncode] using h

/-- Reinsert a raw encoded fieldword; no coefficient decoder or encoder runs. -/
theorem machine_push {V : Type} (e : Encoding V Bool) (x : V) (s : List V) :
    RunsExactly machine.computer.step
      (cfg (6 : Fin 10) () (GraphPreprocessing.Frame.tapes ((stackEncoding e).encode s) (e.encode x) []))
      (cfg (3 : Fin 10) () (GraphPreprocessing.Frame.tapes ((stackEncoding e).encode (x :: s)) [] []))
      (2 * (e.encode x).length + 4) := by
  have h := push_exact (1 : Fin 3) 0 2 (by decide) (by decide) (by decide)
    machine.computer.step 6 7 8 9 3
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl)
    () (fun _ => []) (e.encode x) ((stackEncoding e).encode s)
  convert h using 1 <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

theorem machine_budget (label : Fin 10) : TM2Cost.budget (machine.program label) ≤ 8 := by
  fin_cases label <;> decide

end Holant.OneHot.StackProgram.Machine.StackWord
