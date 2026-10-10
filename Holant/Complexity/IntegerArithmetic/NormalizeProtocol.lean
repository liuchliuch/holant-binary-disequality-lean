import Holant.Complexity.IntegerArithmetic.CarryProtocol
import Holant.Complexity.BinaryArithmetic.SubtractBits

/-! Actual returning clear/trim/reverse protocols using the signed arithmetic
machine's finite memory. Trimming counts every removed high zero explicitly. -/

namespace Holant.Complexity.IntegerArithmetic.NormalizeProtocol

open Turing BinaryArithmetic CarryProtocol
open Turing.TM2.Stmt
variable {K Λ : Type} [DecidableEq K]

def clearStmt (src : K) (loop : Λ) (next : Signs → Λ) : Statement K Λ :=
  pop src saveBit (branch (fun v => v.1.1.2.1.isSome)
    (load clearBit (goto (fun _ => loop)))
    (load clearBit (goto (fun v => next v.2))))

def trimStmt (src dst : K) (loop reverse : Λ) (next : Signs → Λ) : Statement K Λ :=
  pop src saveBit (branch (fun v => v.1.1.2.1.isSome)
    (branch (fun v => v.1.1.2.1.getD false)
      (push dst (fun _ => true) (load clearBit (goto (fun _ => reverse))))
      (load clearBit (goto (fun _ => loop))))
    (load clearBit (goto (fun v => next v.2))))

variable (dst src : K) (hds : dst ≠ src)

theorem clear_cons (step : Config K Λ → Option (Config K Λ)) (loop : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (clearStmt src loop next))
    (signs : Signs) (frame : K → List Bool) (b : Bool) (word out : List Bool) :
    step (cfg loop signs (tapes2 frame dst src out (b :: word))) =
      some (cfg loop signs (tapes2 frame dst src out word)) := by
  rw [cfg, h]
  simp [clearStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]

theorem clear_nil (step : Config K Λ → Option (Config K Λ)) (loop : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (clearStmt src loop next))
    (signs : Signs) (frame : K → List Bool) (out : List Bool) :
    step (cfg loop signs (tapes2 frame dst src out [])) =
      some (cfg (next signs) signs (tapes2 frame dst src out [])) := by
  rw [cfg, h]
  simp [clearStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]

theorem clear_exact (step : Config K Λ → Option (Config K Λ)) (loop : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (clearStmt src loop next))
    (signs : Signs) (frame : K → List Bool) (word out : List Bool) :
    Runs step (cfg loop signs (tapes2 frame dst src out word))
      (cfg (next signs) signs (tapes2 frame dst src out [])) (word.length + 1) := by
  induction word with
  | nil => exact Runs.one (clear_nil dst src step loop next h signs frame out)
  | cons bit word ih => exact (Runs.one (clear_cons dst src step loop next h signs frame bit word out)).trans ih

theorem trim_false (step : Config K Λ → Option (Config K Λ)) (loop reverse : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (trimStmt src dst loop reverse next))
    (signs : Signs) (frame : K → List Bool) (word : List Bool) :
    step (cfg loop signs (tapes2 frame dst src [] (false :: word))) =
      some (cfg loop signs (tapes2 frame dst src [] word)) := by
  rw [cfg, h]
  simp [trimStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]

include hds in
theorem trim_true (step : Config K Λ → Option (Config K Λ)) (loop reverse : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (trimStmt src dst loop reverse next))
    (signs : Signs) (frame : K → List Bool) (word : List Bool) :
    step (cfg loop signs (tapes2 frame dst src [] (true :: word))) =
      some (cfg reverse signs (tapes2 frame dst src [true] word)) := by
  rw [cfg, h]
  simp [trimStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial,
    tapes2_src dst src hds, update_src dst src hds]

theorem trim_nil (step : Config K Λ → Option (Config K Λ)) (loop reverse : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (trimStmt src dst loop reverse next))
    (signs : Signs) (frame : K → List Bool) :
    step (cfg loop signs (tapes2 frame dst src [] [])) =
      some (cfg (next signs) signs (tapes2 frame dst src [] [])) := by
  rw [cfg, h]
  simp [trimStmt, TM2.stepAux, cfg, saveBit, clearBit, clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]

include hds in
theorem normalize_exact (step : Config K Λ → Option (Config K Λ)) (loop reverse : Λ) (next : Signs → Λ)
    (ht : ExecutesAt step loop (trimStmt src dst loop reverse next))
    (hr : ExecutesAt step reverse (restoreStmt dst src reverse next))
    (signs : Signs) (frame : K → List Bool) (word : List Bool) :
    Runs step (cfg loop signs (tapes2 frame dst src [] word))
      (cfg (next signs) signs (tapes2 frame dst src (normalize word.reverse) [])) (word.length + 1) := by
  induction word with
  | nil => simpa using Runs.one (trim_nil dst src step loop reverse next ht signs frame)
  | cons bit word ih =>
    cases bit
    · have h := (Runs.one (trim_false dst src step loop reverse next ht signs frame word)).trans ih
      simpa using h
    · have h := (Runs.one (trim_true dst src hds step loop reverse next ht signs frame word)).trans
        (restore_exact dst src hds step reverse next hr signs frame word [true])
      simpa [List.reverse_cons] using h

end Holant.Complexity.IntegerArithmetic.NormalizeProtocol
