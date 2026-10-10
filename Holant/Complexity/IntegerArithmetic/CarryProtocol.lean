import Holant.Complexity.IntegerArithmetic.CarryBits
import Holant.Complexity.BinaryArithmetic.Multiplication

/-! Returning carry and borrow routines on actual binary stacks. Only a finite
optional-bit register and two saved sign bits are used. The source word is
updated in place; scratch emptiness and all other stacks are preserved. -/

namespace Holant.Complexity.IntegerArithmetic.CarryProtocol

open Turing BinaryArithmetic
open Turing.TM2.Stmt

abbrev Signs := Bool × Bool
abbrev Memory := Multiplication.Memory × Signs
variable {K Λ : Type} [DecidableEq K]
abbrev Config (K Λ : Type) := TM2.Cfg (fun _ : K => Bool) Λ Memory
abbrev Statement (K Λ : Type) := TM2.Stmt (fun _ : K => Bool) Λ Memory

def clean (signs : Signs) : Memory := (Multiplication.clean, signs)
def saveBit (v : Memory) (bit : Option Bool) : Memory := (Multiplication.saveBit v.1 bit, v.2)
def clearBit (v : Memory) : Memory := clean v.2

def cfg (label : Λ) (signs : Signs) (tapes : K → List Bool) : Config K Λ :=
  ⟨some label, clean signs, tapes⟩

def ExecutesAt (step : Config K Λ → Option (Config K Λ)) (label : Λ) (stmt : Statement K Λ) : Prop :=
  ∀ v tapes, step ⟨some label, v, tapes⟩ = some (TM2.stepAux stmt v tapes)

def incrementStmt (src tmp : K) (loop restore : Λ) : Statement K Λ :=
  pop src saveBit
    (branch (fun v => v.1.1.2.1.getD false)
      (push tmp (fun _ => false) (load clearBit (goto (fun _ => loop))))
      (push src (fun _ => true) (load clearBit (goto (fun _ => restore)))))

def decrementStmt (src tmp : K) (loop restore : Λ) : Statement K Λ :=
  pop src saveBit
    (branch (fun v => v.1.1.2.1.isSome)
      (branch (fun v => v.1.1.2.1.getD false)
        (peek src saveBit
          (branch (fun v => v.1.1.2.1.isSome)
            (push src (fun _ => false) (load clearBit (goto (fun _ => restore))))
            (load clearBit (goto (fun _ => restore)))))
        (push tmp (fun _ => true) (load clearBit (goto (fun _ => loop)))))
      (load clearBit (goto (fun _ => restore))))

def restoreStmt (src tmp : K) (loop : Λ) (next : Signs → Λ) : Statement K Λ :=
  pop tmp saveBit
    (branch (fun v => v.1.1.2.1.isSome)
      (push src (fun v => v.1.1.2.1.getD false) (load clearBit (goto (fun _ => loop))))
      (load clearBit (goto (fun v => next v.2))))

def tapes2 (frame : K → List Bool) (src tmp : K) (word scratch : List Bool) : K → List Bool :=
  Function.update (Function.update frame src word) tmp scratch

variable (src tmp : K) (hst : src ≠ tmp)

include hst in
@[simp] theorem tapes2_src (frame : K → List Bool) (word scratch : List Bool) :
    tapes2 frame src tmp word scratch src = word := by simp [tapes2, hst]
@[simp] theorem tapes2_tmp (frame : K → List Bool) (word scratch : List Bool) :
    tapes2 frame src tmp word scratch tmp = scratch := by simp [tapes2]

include hst in
@[simp] theorem update_src (frame : K → List Bool) (word scratch new : List Bool) :
    Function.update (tapes2 frame src tmp word scratch) src new = tapes2 frame src tmp new scratch := by
  funext k
  by_cases hk : k = src
  · subst k; simp [tapes2, hst]
  · simp [tapes2, Function.update_apply, hk]
@[simp] theorem update_tmp (frame : K → List Bool) (word scratch new : List Bool) :
    Function.update (tapes2 frame src tmp word scratch) tmp new = tapes2 frame src tmp word new := by
  simp [tapes2, Function.update_idem]

def Runs (step : Config K Λ → Option (Config K Λ)) (a b : Config K Λ) (n : ℕ) : Prop :=
  (fun c => c.bind step)^[n] (some a) = some b

omit [DecidableEq K] in
theorem Runs.one {step : Config K Λ → Option (Config K Λ)} {a b : Config K Λ}
    (h : step a = some b) : Runs step a b 1 := h

omit [DecidableEq K] in
theorem Runs.trans {step : Config K Λ → Option (Config K Λ)} {a b c : Config K Λ} {n m : ℕ}
    (h : Runs step a b n) (h' : Runs step b c m) : Runs step a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

include hst in
theorem increment_true (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (incrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (word scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp (true :: word) scratch)) =
      some (cfg loop signs (tapes2 frame src tmp word (false :: scratch))) := by
  rw [cfg, h]
  simp [incrementStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst]

include hst in
theorem increment_false (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (incrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (word scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp (false :: word) scratch)) =
      some (cfg restore signs (tapes2 frame src tmp (true :: word) scratch)) := by
  rw [cfg, h]
  simp [incrementStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst]

include hst in
theorem increment_nil (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (incrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp [] scratch)) =
      some (cfg restore signs (tapes2 frame src tmp [true] scratch)) := by
  rw [cfg, h]
  simp [incrementStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst]

include hst in
theorem decrement_false (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (decrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (word scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp (false :: word) scratch)) =
      some (cfg loop signs (tapes2 frame src tmp word (true :: scratch))) := by
  rw [cfg, h]
  simp [decrementStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst]

include hst in
theorem decrement_true (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (decrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (word scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp (true :: word) scratch)) =
      some (cfg restore signs (tapes2 frame src tmp (Doubling.shift word) scratch)) := by
  cases word <;> rw [cfg, h] <;>
    simp [decrementStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
      Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst, Doubling.shift]

include hst in
theorem decrement_nil (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (decrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp [] scratch)) =
      some (cfg restore signs (tapes2 frame src tmp [] scratch)) := by
  rw [cfg, h]
  simp [decrementStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst]

include hst in
theorem restore_cons (step : Config K Λ → Option (Config K Λ)) (loop : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (restoreStmt src tmp loop next))
    (signs : Signs) (frame : K → List Bool) (bit : Bool) (word scratch : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp word (bit :: scratch))) =
      some (cfg loop signs (tapes2 frame src tmp (bit :: word) scratch)) := by
  rw [cfg, h]
  simp [restoreStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial, tapes2_src src tmp hst, update_src src tmp hst]

theorem restore_nil (step : Config K Λ → Option (Config K Λ)) (loop : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (restoreStmt src tmp loop next))
    (signs : Signs) (frame : K → List Bool) (word : List Bool) :
    step (cfg loop signs (tapes2 frame src tmp word [])) =
      some (cfg (next signs) signs (tapes2 frame src tmp word [])) := by
  rw [cfg, h]
  simp [restoreStmt, TM2.stepAux, cfg, saveBit, clearBit, clean, Multiplication.saveBit,
    Multiplication.clean, Addition.initial]

include hst in
theorem increment_move_exact (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (incrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (word scratch : List Bool) :
    Runs step (cfg loop signs (tapes2 frame src tmp word scratch))
      (cfg restore signs (tapes2 frame src tmp (carryTail word)
        (List.replicate (carryCount word) false ++ scratch))) (carryCount word + 1) := by
  induction word generalizing scratch with
  | nil => simpa [carryTail, carryCount] using Runs.one (increment_nil src tmp hst step loop restore h signs frame scratch)
  | cons bit word ih =>
    cases bit
    · simpa [carryTail, carryCount] using Runs.one (increment_false src tmp hst step loop restore h signs frame word scratch)
    · have run := (Runs.one (increment_true src tmp hst step loop restore h signs frame word scratch)).trans
        (ih (false :: scratch))
      simpa [carryTail, carryCount, List.replicate_add, List.append_assoc] using run

include hst in
theorem decrement_move_exact (step : Config K Λ → Option (Config K Λ)) (loop restore : Λ)
    (h : ExecutesAt step loop (decrementStmt src tmp loop restore))
    (signs : Signs) (frame : K → List Bool) (word scratch : List Bool) :
    Runs step (cfg loop signs (tapes2 frame src tmp word scratch))
      (cfg restore signs (tapes2 frame src tmp (borrowTail word)
        (List.replicate (borrowCount word) true ++ scratch))) (borrowCount word + 1) := by
  induction word generalizing scratch with
  | nil => simpa [borrowTail, borrowCount] using Runs.one (decrement_nil src tmp hst step loop restore h signs frame scratch)
  | cons bit word ih =>
    cases bit
    · have run := (Runs.one (decrement_false src tmp hst step loop restore h signs frame word scratch)).trans
        (ih (true :: scratch))
      simpa [borrowTail, borrowCount, List.replicate_add, List.append_assoc] using run
    · simpa [borrowTail, borrowCount] using Runs.one (decrement_true src tmp hst step loop restore h signs frame word scratch)

include hst in
theorem restore_exact (step : Config K Λ → Option (Config K Λ)) (loop : Λ) (next : Signs → Λ)
    (h : ExecutesAt step loop (restoreStmt src tmp loop next))
    (signs : Signs) (frame : K → List Bool) (scratch word : List Bool) :
    Runs step (cfg loop signs (tapes2 frame src tmp word scratch))
      (cfg (next signs) signs (tapes2 frame src tmp (scratch.reverse ++ word) [])) (scratch.length + 1) := by
  induction scratch generalizing word with
  | nil => simpa using Runs.one (restore_nil src tmp step loop next h signs frame word)
  | cons bit scratch ih =>
    have run := (Runs.one (restore_cons src tmp hst step loop next h signs frame bit word scratch)).trans (ih (bit :: word))
    simpa [List.reverse_cons, List.append_assoc] using run

include hst in
theorem increment_exact_frame (step : Config K Λ → Option (Config K Λ))
    (loop restore : Λ) (next : Signs → Λ)
    (hl : ExecutesAt step loop (incrementStmt src tmp loop restore))
    (hr : ExecutesAt step restore (restoreStmt src tmp restore next))
    (signs : Signs) (frame : K → List Bool) (word : List Bool) :
    Runs step (cfg loop signs (tapes2 frame src tmp word []))
      (cfg (next signs) signs (tapes2 frame src tmp (increment word) [])) (2 * (carryCount word + 1)) := by
  have h := increment_move_exact src tmp hst step loop restore hl signs frame word []
  simp only [List.append_nil] at h
  have run := h.trans (restore_exact src tmp hst step restore next hr signs frame
    (List.replicate (carryCount word) false) (carryTail word))
  simpa [← increment_split, Nat.two_mul] using run

include hst in
theorem decrement_exact_frame (step : Config K Λ → Option (Config K Λ))
    (loop restore : Λ) (next : Signs → Λ)
    (hl : ExecutesAt step loop (decrementStmt src tmp loop restore))
    (hr : ExecutesAt step restore (restoreStmt src tmp restore next))
    (signs : Signs) (frame : K → List Bool) (word : List Bool) :
    Runs step (cfg loop signs (tapes2 frame src tmp word []))
      (cfg (next signs) signs (tapes2 frame src tmp (decrement word) [])) (2 * (borrowCount word + 1)) := by
  have h := decrement_move_exact src tmp hst step loop restore hl signs frame word []
  simp only [List.append_nil] at h
  have run := h.trans (restore_exact src tmp hst step restore next hr signs frame
    (List.replicate (borrowCount word) true) (borrowTail word))
  simpa [← decrement_split, Nat.two_mul] using run

end Holant.Complexity.IntegerArithmetic.CarryProtocol
