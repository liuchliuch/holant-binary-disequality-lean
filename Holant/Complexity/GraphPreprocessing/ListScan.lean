import Holant.Complexity.GraphPreprocessing.Frame

/-! Returning traversal of the actual framed-list codec. List markers allocate
one Boolean counter bit per entry. Payload framing is consumed symbol by symbol;
no element decoder or natural-valued identifier controls the traversal. The
counter is bounded by the physical input, including on malformed inputs. -/

namespace Holant.Complexity.GraphPreprocessing.ListScan
open Turing Holant.Algebraic StackProtocol Computability
open Turing.TM2.Stmt

variable {K Λ τ : Type} [DecidableEq K]

/-- A list marker is inspected only after checking that a bit exists. -/
def markerStmt (src count : K) (loop skip good bad : Λ) : Stmt K Λ τ :=
  pop src (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (push count (fun _ => true)
          (load (fun v => (none, v.2)) (goto (fun _ => skip))))
        (load (fun v => (none, v.2)) (goto (fun _ => good))))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

/-- Discard an element's framed payload without interpreting its potentially huge ID. -/
def skipStmt (src : K) (loop good bad : Λ) : Stmt K Λ τ :=
  pop src (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (branch (fun v => v.1.getD false)
        (pop src (fun v b => (b, v.2))
          (branch (fun v => v.1.isSome)
            (load (fun v => (none, v.2)) (goto (fun _ => loop)))
            (load (fun v => (none, v.2)) (goto (fun _ => bad)))))
        (load (fun v => (none, v.2)) (goto (fun _ => good))))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

omit [DecidableEq K] in
@[simp] theorem markerStmt_budget (src count : K) (loop skip good bad : Λ) :
    TM2Cost.budget (markerStmt (τ := τ) src count loop skip good bad) = 6 := rfl

omit [DecidableEq K] in
@[simp] theorem skipStmt_budget (src : K) (loop good bad : Λ) :
    TM2Cost.budget (skipStmt (τ := τ) src loop good bad) = 7 := rfl

def tapes2 (frame : K → List Bool) (src count : K) (input counter : List Bool) : K → List Bool :=
  Function.update (Function.update frame src input) count counter

variable (src count : K) (hne : src ≠ count)

include hne in
@[simp] theorem tapes2_src (frame : K → List Bool) (input counter : List Bool) :
    tapes2 frame src count input counter src = input := by simp [tapes2, hne]

@[simp] theorem tapes2_count (frame : K → List Bool) (input counter : List Bool) :
    tapes2 frame src count input counter count = counter := by simp [tapes2]

include hne in
@[simp] theorem update_src (frame : K → List Bool) (input counter new : List Bool) :
    Function.update (tapes2 frame src count input counter) src new =
      tapes2 frame src count new counter := by
  funext k
  by_cases h : k = src
  · subst k; simp [tapes2, hne]
  · simp [tapes2, Function.update_apply, h]

@[simp] theorem update_count (frame : K → List Bool) (input counter new : List Bool) :
    Function.update (tapes2 frame src count input counter) count new =
      tapes2 frame src count input new := by simp [tapes2, Function.update_idem]

section Skip
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop good bad : Λ)
variable (hs : ExecutesAt step loop (skipStmt src loop good bad))
include hs hne

theorem skip_pair (memory : τ) (frame : K → List Bool)
    (bit : Bool) (input counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count (true :: bit :: input) counter)) =
      some (cfg loop memory (tapes2 frame src count input counter)) := by
  rw [cfg, hs]
  simp [skipStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

theorem skip_terminator (memory : τ) (frame : K → List Bool) (input counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count (false :: input) counter)) =
      some (cfg good memory (tapes2 frame src count input counter)) := by
  rw [cfg, hs]
  simp [skipStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

theorem skip_eof (memory : τ) (frame : K → List Bool) (counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count [] counter)) =
      some (cfg bad memory (tapes2 frame src count [] counter)) := by
  rw [cfg, hs]
  simp [skipStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

theorem skip_truncated (memory : τ) (frame : K → List Bool) (counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count [true] counter)) =
      some (cfg bad memory (tapes2 frame src count [] counter)) := by
  rw [cfg, hs]
  simp [skipStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

theorem skip_exact (memory : τ) (frame : K → List Bool) (word suffix counter : List Bool) :
    RunsExactly step (cfg loop memory (tapes2 frame src count (Holant.Algebraic.frame word ++ suffix) counter))
      (cfg good memory (tapes2 frame src count suffix counter)) (word.length + 1) := by
  induction word with
  | nil => simpa [Holant.Algebraic.frame] using
      (runsExactly_one (skip_terminator src count hne step loop good bad hs memory frame suffix counter))
  | cons bit word ih =>
    exact (runsExactly_one (skip_pair src count hne step loop good bad hs memory frame bit
      (Holant.Algebraic.frame word ++ suffix) counter)).trans ih

theorem skip_rejects (memory : τ) (frame : K → List Bool)
    (input counter : List Bool) (h : unframe input = none) :
    ∃ time, time ≤ input.length + 1 ∧
      RunsExactly step (cfg loop memory (tapes2 frame src count input counter))
        (cfg bad memory (tapes2 frame src count [] counter)) time := by
  induction input using unframe.induct with
  | case1 => exact ⟨1, by simp, runsExactly_one (skip_eof src count hne step loop good bad hs memory frame counter)⟩
  | case2 rest => simp [unframe] at h
  | case3 => exact ⟨1, by simp, runsExactly_one (skip_truncated src count hne step loop good bad hs memory frame counter)⟩
  | case4 bit rest ih =>
    obtain ⟨time, ht, hr⟩ := ih (by simpa [unframe] using h)
    exact ⟨time + 1, by simp only [List.length_cons]; omega,
      (runsExactly_one (skip_pair src count hne step loop good bad hs memory frame bit rest counter)).trans hr⟩
end Skip

section Count
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (loop skip good bad : Λ)
variable (hm : ExecutesAt step loop (markerStmt src count loop skip good bad))
include hm hne

theorem marker_entry (memory : τ) (frame : K → List Bool) (input counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count (true :: input) counter)) =
      some (cfg skip memory (tapes2 frame src count input (true :: counter))) := by
  rw [cfg, hm]
  simp [markerStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

theorem marker_end (memory : τ) (frame : K → List Bool) (input counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count (false :: input) counter)) =
      some (cfg good memory (tapes2 frame src count input counter)) := by
  rw [cfg, hm]
  simp [markerStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

theorem marker_eof (memory : τ) (frame : K → List Bool) (counter : List Bool) :
    step (cfg loop memory (tapes2 frame src count [] counter)) =
      some (cfg bad memory (tapes2 frame src count [] counter)) := by
  rw [cfg, hm]
  simp [markerStmt, TM2.stepAux, cfg, tapes2_src src count hne, update_src src count hne]

omit [DecidableEq K] hm hne in
/-- A count of actual loop transitions, later proved to match execution exactly. -/
def ticks {α : Type} (e : Encoding α Bool) : List α → ℕ
  | [] => 1
  | a :: xs => (e.encode a).length + 2 + ticks e xs

omit [DecidableEq K] hm hne in
theorem ticks_le_length {α : Type} (e : Encoding α Bool) (xs : List α) :
    ticks e xs ≤ (framedListEncode e xs).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [ticks, framedListEncode, List.length_cons, List.length_append, frame_length]; omega

variable (hs : ExecutesAt step skip (skipStmt src skip loop bad))
include hs

/-- List traversal, payload skipping, counter allocation and terminator are all executed. -/
theorem count_exact {α : Type} (e : Encoding α Bool) (memory : τ) (frame : K → List Bool)
    (xs : List α) (suffix counter : List Bool) :
    RunsExactly step (cfg loop memory (tapes2 frame src count (framedListEncode e xs ++ suffix) counter))
      (cfg good memory (tapes2 frame src count suffix (List.replicate xs.length true ++ counter)))
      (ticks e xs) := by
  induction xs generalizing counter with
  | nil => simpa [framedListEncode, ticks] using
      (runsExactly_one (marker_end src count hne step loop skip good bad hm memory frame suffix counter))
  | cons a xs ih =>
    have first := runsExactly_one (marker_entry src count hne step loop skip good bad hm memory frame
      (Holant.Algebraic.frame (e.encode a) ++ framedListEncode e xs ++ suffix) counter)
    have second := skip_exact src count hne step skip loop bad hs memory frame (e.encode a)
      (framedListEncode e xs ++ suffix) (true :: counter)
    have run := (first.trans (by simpa only [List.append_assoc] using second)).trans (ih (true :: counter))
    convert run using 1
    · simp [framedListEncode, List.append_assoc]
    · congr 2
      rw [List.length_cons, List.replicate_add]
      simp [List.append_assoc]
    · simp [ticks]; omega

end Count
end Holant.Complexity.GraphPreprocessing.ListScan
