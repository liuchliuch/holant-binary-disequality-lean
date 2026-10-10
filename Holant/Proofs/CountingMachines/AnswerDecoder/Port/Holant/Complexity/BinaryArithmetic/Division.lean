import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.BinaryArithmetic.DivideBits
import Holant.Complexity.BinaryArithmetic.Addition


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
open _root_.Holant.Complexity
open _root_.Holant.Complexity.BinaryArithmetic


/-!
# Finite binary long division

A seven-stack machine reads the dividend most-significant-bit first. Each digit
is shifted into the remainder and followed by a binary trial subtraction. The
same pass copies the divisor and old remainder; bounded restoration loops retain
the correct remainder and restore the divisor. Quotient leading zeros are skipped.
Every operation is a finite Boolean-register stack instruction.
-/

namespace Holant.Complexity.BinaryArithmetic.Division

open Turing Computability
open Turing.TM2.Stmt
open DivisionBits

inductive Stack
  | input | divisor | remainder | divisorRev | oldRev | trialRev | quotient
  deriving DecidableEq
instance : Fintype Stack :=
  ⟨{.input, .divisor, .remainder, .divisorRev, .oldRev, .trialRev, .quotient}, by intro k; cases k <;> simp⟩

inductive Label
  | start | next | columns | restoreGood | restoreBad | trimTrial | reverseTrial | reverseOld | zero | finish
  deriving DecidableEq
instance : Fintype Label :=
  ⟨{.start, .next, .columns, .restoreGood, .restoreBad, .trimTrial, .reverseTrial, .reverseOld, .zero, .finish},
    by intro k; cases k <;> simp⟩

abbrev State := Addition.State
abbrev initial := Addition.initial
abbrev reset := Addition.reset
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label State
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label State

def saveFirst (v : State) (bit : Option Bool) : State := (v.1, bit, v.2.2)
def saveSecond (v : State) (bit : Option Bool) : State := (v.1, v.2.1, bit)
def again (label : Label) : Statement := load (fun _ => initial) (goto (fun _ => label))
def ifFirst (stack : Stack) (cont : Statement) : Statement :=
  branch (fun v => v.2.1.isSome) (push stack (fun v => v.2.1.getD false) cont) cont

def program (remainderOutput : Bool) : Label → Statement
  | .start => peek .divisor saveFirst
      (branch (fun v => v.2.1.isSome) (again .next) (again .zero))
  | .next => pop .input saveFirst
      (branch (fun v => v.2.1.isSome)
        (peek .remainder saveSecond
          (branch (fun v => v.2.1.getD false || v.2.2.isSome)
            (push .remainder (fun v => v.2.1.getD false) (again .columns))
            (again .columns)))
        (again .finish))
  | .columns => pop .remainder saveFirst
      (pop .divisor saveSecond
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (push .trialRev (fun v => digitDiff v.1 (v.2.1.getD false) (v.2.2.getD false))
            (ifFirst .oldRev
              (branch (fun v => v.2.2.isSome)
                (push .divisorRev (fun v => v.2.2.getD false)
                  (load (fun v => reset (digitBorrow v.1 (v.2.1.getD false) (v.2.2.getD false)))
                    (goto (fun _ => .columns))))
                (load (fun v => reset (digitBorrow v.1 (v.2.1.getD false) (v.2.2.getD false)))
                  (goto (fun _ => .columns))))))
          (branch (fun v => v.1)
            (peek .quotient saveFirst
              (branch (fun v => v.2.1.isSome)
                (push .quotient (fun _ => false) (again .restoreBad))
                (again .restoreBad)))
            (push .quotient (fun _ => true) (again .restoreGood)))))
  | .restoreGood => pop .divisorRev saveFirst
      (pop .oldRev saveSecond
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (ifFirst .divisor (again .restoreGood)) (again .trimTrial)))
  | .restoreBad => pop .divisorRev saveFirst
      (pop .trialRev saveSecond
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (ifFirst .divisor (again .restoreBad)) (again .reverseOld)))
  | .trimTrial => pop .trialRev saveFirst
      (branch (fun v => v.2.1.isSome)
        (branch (fun v => v.2.1.getD false)
          (push .remainder (fun _ => true) (again .reverseTrial))
          (again .trimTrial))
        (again .next))
  | .reverseTrial => pop .trialRev saveFirst
      (branch (fun v => v.2.1.isSome)
        (push .remainder (fun v => v.2.1.getD false) (again .reverseTrial))
        (again .next))
  | .reverseOld => pop .oldRev saveFirst
      (branch (fun v => v.2.1.isSome)
        (push .remainder (fun v => v.2.1.getD false) (again .reverseOld))
        (again .next))
  | .zero => pop .input saveFirst
      (branch (fun v => v.2.1.isSome)
        (push .remainder (fun v => v.2.1.getD false) (again .zero))
        (again .finish))
  | .finish => pop .divisor saveFirst
      (pop (if remainderOutput then .quotient else .remainder) saveSecond
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (again .finish) (load (fun _ => initial) halt)))

abbrev computer (remainderOutput : Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := if remainderOutput then .remainder else .quotient
  Γ _ := Bool
  Λ := Label
  main := .start
  σ := State
  initialState := initial
  m := program remainderOutput

instance finiteAlphabet (out : Bool) (k : (computer out).K) :
    Fintype ((computer out).Γ k) := inferInstanceAs (Fintype Bool)

def tapes (i d r dr old trial q : List Bool) : Stack → List Bool
  | .input => i
  | .divisor => d
  | .remainder => r
  | .divisorRev => dr
  | .oldRev => old
  | .trialRev => trial
  | .quotient => q

def cfg (label : Option Label) (borrow : Bool) (i d r dr old trial q : List Bool) : Config :=
  ⟨label, reset borrow, tapes i d r dr old trial q⟩

def Runs (out : Bool) (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind (computer out).step)^[n] (some start) = some finish

theorem Runs.one {out : Bool} {a b : Config} (h : (computer out).step a = some b) : Runs out a b 1 := h

theorem Runs.trans {out : Bool} {a b c : Config} {n m : ℕ} (h : Runs out a b n) (h' : Runs out b c m) :
    Runs out a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

@[simp] theorem update_input (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .input x = tapes x d r dr old trial q := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem update_divisor (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .divisor x = tapes i x r dr old trial q := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem update_remainder (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .remainder x = tapes i d x dr old trial q := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem update_divisorRev (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .divisorRev x = tapes i d r x old trial q := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem update_oldRev (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .oldRev x = tapes i d r dr x trial q := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem update_trialRev (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .trialRev x = tapes i d r dr old x q := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem update_quotient (i d r dr old trial q x : List Bool) :
    Function.update (tapes i d r dr old trial q) .quotient x = tapes i d r dr old trial x := by
  funext k; cases k <;> simp [tapes]

@[simp] theorem step_start_nil (out : Bool) (i : List Bool) :
    (computer out).step (cfg (some .start) false i [] [] [] [] [] []) =
      some (cfg (some .zero) false i [] [] [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_start_cons (out bit : Bool) (i d : List Bool) :
    (computer out).step (cfg (some .start) false i (bit :: d) [] [] [] [] []) =
      some (cfg (some .next) false i (bit :: d) [] [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_next_cons (out bit : Bool) (i d r q : List Bool) :
    (computer out).step (cfg (some .next) false (bit :: i) d r [] [] [] q) =
      some (cfg (some .columns) false i d (shiftBit bit r) [] [] [] q) := by
  cases bit <;> cases r <;> simp only [shiftBit] <;> simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again] <;> congr 2

@[simp] theorem step_next_nil (out : Bool) (d r q : List Bool) :
    (computer out).step (cfg (some .next) false [] d r [] [] [] q) =
      some (cfg (some .finish) false [] d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_columns_both (out borrow x y : Bool) (i d r dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i (y :: d) (x :: r) dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow x y) i d r (y :: dr) (x :: old) (digitDiff borrow x y :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_columns_left (out borrow x : Bool) (i r dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i [] (x :: r) dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow x false) i [] r dr (x :: old) (digitDiff borrow x false :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_columns_right (out borrow y : Bool) (i d dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i (y :: d) [] dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow false y) i d [] (y :: dr) old (digitDiff borrow false y :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_columns_done (out borrow : Bool) (i dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i [] [] dr old trial q) =
      some (cfg (some (if borrow then .restoreBad else .restoreGood)) false i [] [] dr old trial (shiftBit (!borrow) q)) := by
  cases borrow <;> cases q <;> simp only [shiftBit] <;> simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst] <;> congr 2

/-- One bitwise subtraction pass also copies both consumed operands. -/
theorem columns_exact (out borrow : Bool) (i d r dr old trial q : List Bool) :
    Runs out (cfg (some .columns) borrow i d r dr old trial q)
      (cfg (some (if (subBits borrow r d).2 then .restoreBad else .restoreGood)) false
        i [] [] (d.reverse ++ dr) (r.reverse ++ old)
        ((subBits borrow r d).1.reverse ++ trial) (shiftBit (!(subBits borrow r d).2) q))
      (max r.length d.length + 1) := by
  induction r generalizing d borrow dr old trial with
  | nil =>
    induction d generalizing borrow dr trial with
    | nil => simpa [subBits] using Runs.one (step_columns_done out borrow i dr old trial q)
    | cons y d ih =>
      have h := (Runs.one (step_columns_right out borrow y i d dr old trial q)).trans
        (ih (digitBorrow borrow false y) (y :: dr) (digitDiff borrow false y :: trial))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
  | cons x r ih =>
    cases d with
    | nil =>
      have h := (Runs.one (step_columns_left out borrow x i r dr old trial q)).trans
        (ih (digitBorrow borrow x false) [] dr (x :: old) (digitDiff borrow x false :: trial))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
    | cons y d =>
      have h := (Runs.one (step_columns_both out borrow x y i d r dr old trial q)).trans
        (ih (digitBorrow borrow x y) d (y :: dr) (x :: old) (digitDiff borrow x y :: trial))
      simpa [subBits, List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_restore_good_both (out x y : Bool) (i d dr bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] (x :: dr) (y :: bs) fixed q) =
      some (cfg (some .restoreGood) false i (x :: d) [] dr bs fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_good_left (out x : Bool) (i d dr fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] (x :: dr) [] fixed q) =
      some (cfg (some .restoreGood) false i (x :: d) [] dr [] fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_good_right (out y : Bool) (i d bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] [] (y :: bs) fixed q) =
      some (cfg (some .restoreGood) false i d [] [] bs fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_good_nil (out : Bool) (i d fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] [] [] fixed q) =
      some (cfg (some .trimTrial) false i d [] [] [] fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

/-- Restore the divisor while discarding the rejected work word. -/
theorem restore_good_exact (out : Bool) (i d dr bs fixed q : List Bool) :
    Runs out (cfg (some .restoreGood) false i d [] dr bs fixed q)
      (cfg (some .trimTrial) false i (dr.reverse ++ d) [] [] [] fixed q)
      (max dr.length bs.length + 1) := by
  induction dr generalizing bs d with
  | nil =>
    induction bs with
    | nil => simpa using Runs.one (step_restore_good_nil out i d fixed q)
    | cons y bs ih =>
      have h := (Runs.one (step_restore_good_right out y i d bs fixed q)).trans ih
      simpa using h
  | cons x dr ih =>
    cases bs with
    | nil =>
      have h := (Runs.one (step_restore_good_left out x i d dr fixed q)).trans (ih (x :: d) [])
      simpa [List.reverse_cons, List.append_assoc] using h
    | cons y bs =>
      have h := (Runs.one (step_restore_good_both out x y i d dr bs fixed q)).trans (ih (x :: d) bs)
      simpa [List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_restore_bad_both (out x y : Bool) (i d dr bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] (x :: dr) fixed (y :: bs) q) =
      some (cfg (some .restoreBad) false i (x :: d) [] dr fixed bs q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_bad_left (out x : Bool) (i d dr fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] (x :: dr) fixed [] q) =
      some (cfg (some .restoreBad) false i (x :: d) [] dr fixed [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_bad_right (out y : Bool) (i d bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] [] fixed (y :: bs) q) =
      some (cfg (some .restoreBad) false i d [] [] fixed bs q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_bad_nil (out : Bool) (i d fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] [] fixed [] q) =
      some (cfg (some .reverseOld) false i d [] [] fixed [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

/-- Restore the divisor while discarding the rejected work word. -/
theorem restore_bad_exact (out : Bool) (i d dr bs fixed q : List Bool) :
    Runs out (cfg (some .restoreBad) false i d [] dr fixed bs q)
      (cfg (some .reverseOld) false i (dr.reverse ++ d) [] [] fixed [] q)
      (max dr.length bs.length + 1) := by
  induction dr generalizing bs d with
  | nil =>
    induction bs with
    | nil => simpa using Runs.one (step_restore_bad_nil out i d fixed q)
    | cons y bs ih =>
      have h := (Runs.one (step_restore_bad_right out y i d bs fixed q)).trans ih
      simpa using h
  | cons x dr ih =>
    cases bs with
    | nil =>
      have h := (Runs.one (step_restore_bad_left out x i d dr fixed q)).trans (ih (x :: d) [])
      simpa [List.reverse_cons, List.append_assoc] using h
    | cons y bs =>
      have h := (Runs.one (step_restore_bad_both out x y i d dr bs fixed q)).trans (ih (x :: d) bs)
      simpa [List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_reverse_trial_cons (out x : Bool) (i d r w q : List Bool) :
    (computer out).step (cfg (some .reverseTrial) false i d r [] [] (x :: w) q) =
      some (cfg (some .reverseTrial) false i d (x :: r) [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_reverse_trial_nil (out : Bool) (i d r q : List Bool) :
    (computer out).step (cfg (some .reverseTrial) false i d r [] [] [] q) =
      some (cfg (some .next) false i d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

theorem reverse_trial_exact (out : Bool) (i d r w q : List Bool) :
    Runs out (cfg (some .reverseTrial) false i d r [] [] w q)
      (cfg (some .next) false i d (w.reverse ++ r) [] [] [] q) (w.length + 1) := by
  induction w generalizing r with
  | nil => simpa using Runs.one (step_reverse_trial_nil out i d r q)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_trial_cons out x i d r w q)).trans (ih (x :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_reverse_old_cons (out x : Bool) (i d r w q : List Bool) :
    (computer out).step (cfg (some .reverseOld) false i d r [] (x :: w) [] q) =
      some (cfg (some .reverseOld) false i d (x :: r) [] w [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_reverse_old_nil (out : Bool) (i d r q : List Bool) :
    (computer out).step (cfg (some .reverseOld) false i d r [] [] [] q) =
      some (cfg (some .next) false i d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

theorem reverse_old_exact (out : Bool) (i d r w q : List Bool) :
    Runs out (cfg (some .reverseOld) false i d r [] w [] q)
      (cfg (some .next) false i d (w.reverse ++ r) [] [] [] q) (w.length + 1) := by
  induction w generalizing r with
  | nil => simpa using Runs.one (step_reverse_old_nil out i d r q)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_old_cons out x i d r w q)).trans (ih (x :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_trim_false (out : Bool) (i d w q : List Bool) :
    (computer out).step (cfg (some .trimTrial) false i d [] [] [] (false :: w) q) =
      some (cfg (some .trimTrial) false i d [] [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_trim_true (out : Bool) (i d w q : List Bool) :
    (computer out).step (cfg (some .trimTrial) false i d [] [] [] (true :: w) q) =
      some (cfg (some .reverseTrial) false i d [true] [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_trim_nil (out : Bool) (i d q : List Bool) :
    (computer out).step (cfg (some .trimTrial) false i d [] [] [] [] q) =
      some (cfg (some .next) false i d [] [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

/-- High zeros are explicitly popped before reversing the surviving difference. -/
theorem trim_exact (out : Bool) (i d w q : List Bool) :
    Runs out (cfg (some .trimTrial) false i d [] [] [] w q)
      (cfg (some .next) false i d (normalize w.reverse) [] [] [] q) (w.length + 1) := by
  induction w with
  | nil => simpa using Runs.one (step_trim_nil out i d q)
  | cons x w ih =>
    cases x with
    | false => simpa using (Runs.one (step_trim_false out i d w q)).trans ih
    | true =>
      have h := (Runs.one (step_trim_true out i d w q)).trans (reverse_trial_exact out i d [true] w q)
      simpa [List.reverse_cons, List.append_assoc] using h

/-- The actual digit cost includes restoration and all normalization operations. -/
def digitTime (bit : Bool) (d r : List Bool) : ℕ :=
  let shifted := shiftBit bit r
  let width := max shifted.length d.length
  if (subBits false shifted d).2 then 2 * width + shifted.length + 4
  else 3 * width + 4

/-- A complete input-digit iteration, including trial subtraction and cleanup. -/
theorem digit_exact (out bit : Bool) (i d r q : List Bool) :
    Runs out (cfg (some .next) false (bit :: i) d r [] [] [] q)
      (cfg (some .next) false i d (DivisionBits.step bit d q r).2 [] [] []
        (DivisionBits.step bit d q r).1) (digitTime bit d r) := by
  have h₁ := Runs.one (step_next_cons out bit i d r q)
  have h₂ := columns_exact out false i d (shiftBit bit r) [] [] [] q
  simp only [List.append_nil] at h₂
  cases hb : (subBits false (shiftBit bit r) d).2 with
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h₂
    have h₃ := restore_good_exact out i [] d.reverse (shiftBit bit r).reverse
      (subBits false (shiftBit bit r) d).1.reverse (shiftBit true q)
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₃
    have h₄ := trim_exact out i d (subBits false (shiftBit bit r) d).1.reverse (shiftBit true q)
    simp only [List.reverse_reverse, List.length_reverse, subBits_length] at h₄
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    convert h using 1 <;> simp [DivisionBits.step, digitTime, hb, Nat.max_comm]
    all_goals omega
  | true =>
    simp only [hb, ↓reduceIte, Bool.not_true] at h₂
    have h₃ := restore_bad_exact out i [] d.reverse
      (subBits false (shiftBit bit r) d).1.reverse (shiftBit bit r).reverse (shiftBit false q)
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse, subBits_length] at h₃
    have h₄ := reverse_old_exact out i d [] (shiftBit bit r).reverse (shiftBit false q)
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₄
    have h := ((h₁.trans h₂).trans h₃).trans h₄
    convert h using 1 <;> simp [DivisionBits.step, digitTime, hb, Nat.max_comm]
    all_goals omega

/-- Sum of the proved operational per-digit transition costs. -/
def loopTime (d : List Bool) : List Bool → List Bool → List Bool → ℕ
  | [], _, _ => 0
  | bit :: bits, q, r =>
      let next := DivisionBits.step bit d q r
      digitTime bit d r + loopTime d bits next.1 next.2

theorem loop_exact (out : Bool) (bits d q r : List Bool) :
    Runs out (cfg (some .next) false bits d r [] [] [] q)
      (cfg (some .finish) false [] d (loop d bits q r).2 [] [] [] (loop d bits q r).1)
      (loopTime d bits q r + 1) := by
  induction bits generalizing q r with
  | nil => simpa [loopTime, loop] using Runs.one (step_next_nil out d r q)
  | cons bit bits ih =>
    have h := (digit_exact out bit bits d r q).trans
      (ih (DivisionBits.step bit d q r).1 (DivisionBits.step bit d q r).2)
    simpa [loop, loopTime, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Each digit costs linearly in the larger operand length. -/
theorem digitTime_le (bit : Bool) (d r : List Bool) :
    digitTime bit d r ≤ 3 * max r.length d.length + 7 := by
  have hl := shiftBit_length_le bit r
  dsimp only [digitTime]
  split <;> omega

/-- Quadratic runtime in the number of remaining dividend and divisor bits. -/
theorem loopTime_le (d bits q r : List Bool) :
    loopTime d bits q r ≤ (3 * (max r.length d.length + bits.length) + 4) * bits.length := by
  induction bits generalizing q r with
  | nil => simp [loopTime]
  | cons bit bits ih =>
    have hi := ih (DivisionBits.step bit d q r).1 (DivisionBits.step bit d q r).2
    have hs := step_remainder_length_le bit d q r
    have ht := digitTime_le bit d r
    have hm : max (DivisionBits.step bit d q r).2.length d.length ≤ max r.length d.length + 1 := by omega
    have hc :
        (3 * (max (DivisionBits.step bit d q r).2.length d.length + bits.length) + 4) * bits.length ≤
          (3 * (max r.length d.length + 1 + bits.length) + 4) * bits.length :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [loopTime, List.length_cons]
    calc
      digitTime bit d r + loopTime d bits (DivisionBits.step bit d q r).1 (DivisionBits.step bit d q r).2 ≤
          (3 * max r.length d.length + 7) +
            (3 * (max r.length d.length + 1 + bits.length) + 4) * bits.length := Nat.add_le_add ht (hi.trans hc)
      _ ≤ (3 * (max r.length d.length + (bits.length + 1)) + 4) * (bits.length + 1) := by
        simp only [Nat.mul_add, Nat.add_mul]
        omega

@[simp] theorem step_finish_quotient_both (a b : Bool) (d xs kept : List Bool) :
    (computer false).step (cfg (some .finish) false [] (a :: d) (b :: xs) [] [] [] kept) =
      some (cfg (some .finish) false [] d xs [] [] [] kept) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_finish_quotient_left (a : Bool) (d kept : List Bool) :
    (computer false).step (cfg (some .finish) false [] (a :: d) [] [] [] [] kept) =
      some (cfg (some .finish) false [] d [] [] [] [] kept) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_finish_quotient_right (b : Bool) (xs kept : List Bool) :
    (computer false).step (cfg (some .finish) false [] [] (b :: xs) [] [] [] kept) =
      some (cfg (some .finish) false [] [] xs [] [] [] kept) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_finish_quotient_nil (kept : List Bool) :
    (computer false).step (cfg (some .finish) false [] [] [] [] [] [] kept) =
      some (cfg none false [] [] [] [] [] [] kept) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

theorem finish_quotient_exact (d xs kept : List Bool) :
    Runs false (cfg (some .finish) false [] d xs [] [] [] kept)
      (cfg none false [] [] [] [] [] [] kept) (max d.length xs.length + 1) := by
  induction d generalizing xs with
  | nil =>
    induction xs with
    | nil => simpa using Runs.one (step_finish_quotient_nil kept)
    | cons b xs ih =>
      simpa using (Runs.one (step_finish_quotient_right b xs kept)).trans ih
  | cons a d ih =>
    cases xs with
    | nil => simpa using (Runs.one (step_finish_quotient_left a d kept)).trans (ih [])
    | cons b xs =>
      simpa [Nat.succ_max_succ] using
        (Runs.one (step_finish_quotient_both a b d xs kept)).trans (ih xs)

@[simp] theorem step_finish_remainder_both (a b : Bool) (d xs kept : List Bool) :
    (computer true).step (cfg (some .finish) false [] (a :: d) kept [] [] [] (b :: xs)) =
      some (cfg (some .finish) false [] d kept [] [] [] xs) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_finish_remainder_left (a : Bool) (d kept : List Bool) :
    (computer true).step (cfg (some .finish) false [] (a :: d) kept [] [] [] []) =
      some (cfg (some .finish) false [] d kept [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_finish_remainder_right (b : Bool) (xs kept : List Bool) :
    (computer true).step (cfg (some .finish) false [] [] kept [] [] [] (b :: xs)) =
      some (cfg (some .finish) false [] [] kept [] [] [] xs) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

@[simp] theorem step_finish_remainder_nil (kept : List Bool) :
    (computer true).step (cfg (some .finish) false [] [] kept [] [] [] []) =
      some (cfg none false [] [] kept [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again]
  congr 2

theorem finish_remainder_exact (d xs kept : List Bool) :
    Runs true (cfg (some .finish) false [] d kept [] [] [] xs)
      (cfg none false [] [] kept [] [] [] []) (max d.length xs.length + 1) := by
  induction d generalizing xs with
  | nil =>
    induction xs with
    | nil => simpa using Runs.one (step_finish_remainder_nil kept)
    | cons b xs ih =>
      simpa using (Runs.one (step_finish_remainder_right b xs kept)).trans ih
  | cons a d ih =>
    cases xs with
    | nil => simpa using (Runs.one (step_finish_remainder_left a d kept)).trans (ih [])
    | cons b xs =>
      simpa [Nat.succ_max_succ] using
        (Runs.one (step_finish_remainder_both a b d xs kept)).trans (ih xs)

/-- Every nonoutput stack is empty at the final configuration. -/
def finalCfg (out : Bool) (word : List Bool) : Config :=
  cfg none false [] [] (if out then word else []) [] [] [] (if out then [] else word)

def selected (out : Bool) (qr : List Bool × List Bool) : List Bool :=
  if out then qr.2 else qr.1

theorem finish_exact (out : Bool) (d q r : List Bool) :
    Runs out (cfg (some .finish) false [] d r [] [] [] q)
      (finalCfg out (selected out (q,r)))
      (max d.length (selected (!out) (q,r)).length + 1) := by
  cases out with
  | false => simpa [finalCfg, selected] using finish_quotient_exact d r q
  | true => simpa [finalCfg, selected] using finish_remainder_exact d q r

@[simp] theorem step_zero_cons (out bit : Bool) (bits r : List Bool) :
    (computer out).step (cfg (some .zero) false (bit :: bits) [] r [] [] [] []) =
      some (cfg (some .zero) false bits [] (bit :: r) [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_zero_nil (out : Bool) (r : List Bool) :
    (computer out).step (cfg (some .zero) false [] [] r [] [] [] []) =
      some (cfg (some .finish) false [] [] r [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

/-- Divisor zero returns quotient zero and reconstructs the dividend as remainder. -/
theorem zero_exact (out : Bool) (bits r : List Bool) :
    Runs out (cfg (some .zero) false bits [] r [] [] [] [])
      (cfg (some .finish) false [] [] (bits.reverse ++ r) [] [] [] []) (bits.length + 1) := by
  induction bits generalizing r with
  | nil => simpa using Runs.one (step_zero_nil out r)
  | cons bit bits ih =>
    have h := (Runs.one (step_zero_cons out bit bits r)).trans (ih (bit :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- All digit, initialization and final cleanup transitions. -/
def computeTime (out : Bool) (bits d : List Bool) : ℕ :=
  if d = [] then bits.length + (if out then 0 else bits.length) + 3
  else loopTime d bits [] [] + max d.length (selected (!out) (loop d bits [] [])).length + 3

theorem compute_exact (out : Bool) (bits d : List Bool) (hc : Canonical bits.reverse) :
    Runs out (cfg (some .start) false bits d [] [] [] [] [])
      (finalCfg out (selected out (divideBits bits d))) (computeTime out bits d) := by
  cases d with
  | nil =>
    have h₁ := Runs.one (step_start_nil out bits)
    have h₂ := zero_exact out bits []
    simp only [List.append_nil] at h₂
    have h₃ := finish_exact out [] [] bits.reverse
    have h := (h₁.trans h₂).trans h₃
    have hn := normalize_eq_self bits.reverse hc
    cases out <;>
      convert h using 1 <;> simp [computeTime, divideBits, selected, hn, finalCfg] <;> omega
  | cons bit d =>
    have h₁ := Runs.one (step_start_cons out bit bits d)
    have h₂ := loop_exact out bits (bit :: d) [] []
    have h₃ := finish_exact out (bit :: d) (loop (bit :: d) bits [] []).1 (loop (bit :: d) bits [] []).2
    have h := (h₁.trans h₂).trans h₃
    convert h using 1 <;> simp [computeTime, divideBits]
    all_goals omega

/-- Canonical natural quotient/remainder correctness against actual transitions. -/
theorem compute_encodeNat_exact (out : Bool) (a b : ℕ) :
    Runs out (cfg (some .start) false (encodeNat a).reverse (encodeNat b) [] [] [] [] [])
      (finalCfg out (encodeNat (if out then a % b else a / b)))
      (computeTime out (encodeNat a).reverse (encodeNat b)) := by
  have h := compute_exact out (encodeNat a).reverse (encodeNat b) (by simp)
  rw [divideBits_encodeNat] at h
  cases out <;> simpa [selected] using h

/-- A uniform polynomial bound for every prepared binary input. -/
theorem computeTime_le (out : Bool) (bits d : List Bool) :
    computeTime out bits d ≤
      (3 * (bits.length + d.length) + 7) * bits.length + bits.length + d.length + 4 := by
  have hl := loopTime_le d bits [] []
  have hq := loop_quotient_length_le d bits [] []
  have hr := loop_remainder_length_le d bits [] []
  simp only [List.length_nil, Nat.zero_max, Nat.zero_add] at hl hq hr
  have hs : (selected (!out) (loop d bits [] [])).length ≤ d.length + bits.length := by
    cases out <;> simp [selected] <;> omega
  have hm : max d.length (selected (!out) (loop d bits [] [])).length ≤ d.length + bits.length := by omega
  have hp : 7 * bits.length ≤ (3 * (bits.length + d.length) + 7) * bits.length :=
    Nat.mul_le_mul_right _ (by omega)
  unfold computeTime
  split
  · cases out <;> simp <;> omega
  · calc
      loopTime d bits [] [] + max d.length (selected (!out) (loop d bits [] [])).length + 3 ≤
          (3 * (d.length + bits.length) + 4) * bits.length + (d.length + bits.length) + 3 := by omega
      _ ≤ (3 * (bits.length + d.length) + 7) * bits.length + bits.length + d.length + 4 := by
        simp only [Nat.add_mul, Nat.mul_add]
        omega

/-- Actual finite-machine quotient and remainder computations with a bit-length bound. -/
def compute_timed (out : Bool) (a b : ℕ) :
    StateTransition.EvalsToInTime (computer out).step
      (cfg (some .start) false (encodeNat a).reverse (encodeNat b) [] [] [] [] [])
      (some (finalCfg out (encodeNat (if out then a % b else a / b))))
      ((3 * ((encodeNat a).length + (encodeNat b).length) + 7) * (encodeNat a).length +
        (encodeNat a).length + (encodeNat b).length + 4) where
  steps := computeTime out (encodeNat a).reverse (encodeNat b)
  evals_in_steps := compute_encodeNat_exact out a b
  steps_le_m := by simpa using computeTime_le out (encodeNat a).reverse (encodeNat b)

/-- Prepared output has exactly the finite computer's canonical clean halt layout. -/
theorem finalCfg_halt (out : Bool) (word : List Bool) :
    finalCfg out word = haltList (computer out) word := by
  cases out <;> dsimp [finalCfg, cfg, haltList, computer, reset, initial]
  all_goals
    congr 1
    funext k
    cases k <;> rfl

theorem program_budget (out : Bool) (label : Label) : TM2Cost.budget (program out label) ≤ 12 := by
  cases out <;> cases label <;> decide

@[simp] theorem stack_count (out : Bool) : Fintype.card (computer out).K = 7 := by cases out <;> decide
@[simp] theorem label_count (out : Bool) : Fintype.card (computer out).Λ = 10 := by cases out <;> decide
@[simp] theorem state_count (out : Bool) : Fintype.card (computer out).σ = 18 := by cases out <;> decide

end Holant.Complexity.BinaryArithmetic.Division

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
