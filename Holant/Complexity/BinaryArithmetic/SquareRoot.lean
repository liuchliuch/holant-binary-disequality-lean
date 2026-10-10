import Holant.Complexity.BinaryArithmetic.SquareRootBits
import Holant.Complexity.BinaryArithmetic.Addition

/-! A finite Boolean-stack restoring square-root machine. Every radix-four digit
uses one trial subtraction and explicit restoration. The root stack is temporarily
the threshold 4q+1; the trial result determines its next low bit. -/

namespace Holant.Complexity.BinaryArithmetic.SquareRoot

open Turing Computability
open Turing.TM2.Stmt
open DivisionBits SquareRootBits

inductive Stack
  | input | divisor | remainder | divisorRev | oldRev | trialRev | quotient
  deriving DecidableEq
instance : Fintype Stack :=
  ⟨{.input, .divisor, .remainder, .divisorRev, .oldRev, .trialRev, .quotient}, by intro k; cases k <;> simp⟩

inductive Label
  | next | columns | restoreGood | restoreBad | trimTrial | reverseTrial | reverseOld | root | finish
  deriving DecidableEq
instance : Fintype Label :=
  ⟨{.next, .columns, .restoreGood, .restoreBad, .trimTrial, .reverseTrial, .reverseOld, .root, .finish},
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

def shiftFirst (k : Stack) (cont : Statement) : Statement :=
  peek k saveSecond
    (branch (fun v => v.2.1.getD false || v.2.2.isSome)
      (push k (fun v => v.2.1.getD false) cont) cont)

def makeThreshold : Statement :=
  peek .divisor saveFirst
    (branch (fun v => v.2.1.isSome)
      (push .divisor (fun _ => false) (push .divisor (fun _ => true) (again .columns)))
      (push .divisor (fun _ => true) (again .columns)))

def program (remainderOutput : Option Bool) : Label → Statement
  | .next => pop .input saveFirst
      (branch (fun v => v.2.1.isSome)
        (shiftFirst .remainder
          (pop .input saveFirst (shiftFirst .remainder makeThreshold)))
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
        (again .root))
  | .reverseTrial => pop .trialRev saveFirst
      (branch (fun v => v.2.1.isSome)
        (push .remainder (fun v => v.2.1.getD false) (again .reverseTrial))
        (again .root))
  | .reverseOld => pop .oldRev saveFirst
      (branch (fun v => v.2.1.isSome)
        (push .remainder (fun v => v.2.1.getD false) (again .reverseOld))
        (again .root))
  | .root => pop .divisor saveFirst
      (pop .divisor saveFirst
        (pop .quotient saveFirst (shiftFirst .divisor (again .next))))
  | .finish => match remainderOutput with
      | none => load (fun _ => initial) halt
      | some out => pop (if out then .divisor else .remainder) saveFirst
          (branch (fun v => v.2.1.isSome) (again .finish)
            (load (fun _ => initial) halt))

abbrev computer (remainderOutput : Option Bool) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := if remainderOutput = some true then .remainder else .divisor
  Γ _ := Bool
  Λ := Label
  main := .next
  σ := State
  initialState := initial
  m := program remainderOutput

instance finiteAlphabet (out : Option Bool) (k : (computer out).K) :
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

def Runs (out : Option Bool) (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind (computer out).step)^[n] (some start) = some finish

theorem Runs.one {out : Option Bool} {a b : Config} (h : (computer out).step a = some b) : Runs out a b 1 := h

theorem Runs.trans {out : Option Bool} {a b c : Config} {n m : ℕ} (h : Runs out a b n) (h' : Runs out b c m) :
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

@[simp] theorem step_next_pair (out : Option Bool) (hi lo : Bool) (i q r : List Bool) :
    (computer out).step (cfg (some .next) false (hi :: lo :: i) q r [] [] [] []) =
      some (cfg (some .columns) false i (threshold q) (trialWord (hi, lo) r) [] [] [] []) := by
  cases hi <;> cases lo <;> cases q <;> cases r <;>
    simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
      tapes, saveFirst, saveSecond, again, shiftFirst, makeThreshold, trialWord, threshold, shiftBit] <;> congr 2

@[simp] theorem step_next_nil (out : Option Bool) (q r : List Bool) :
    (computer out).step (cfg (some .next) false [] q r [] [] [] []) =
      some (cfg (some .finish) false [] q r [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
    tapes, saveFirst, saveSecond, again, shiftFirst, makeThreshold]
  congr 2

@[simp] theorem step_root (out : Option Bool) (bit : Bool) (i q r : List Bool) :
    (computer out).step (cfg (some .root) false i (threshold q) r [] [] [] (shiftBit bit [])) =
      some (cfg (some .next) false i (shiftBit bit q) r [] [] [] []) := by
  cases bit <;> cases q <;>
    simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
      tapes, saveFirst, saveSecond, again, shiftFirst, threshold, shiftBit] <;> congr 2

@[simp] theorem step_columns_both (out : Option Bool) (borrow x y : Bool) (i d r dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i (y :: d) (x :: r) dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow x y) i d r (y :: dr) (x :: old) (digitDiff borrow x y :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_columns_left (out : Option Bool) (borrow x : Bool) (i r dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i [] (x :: r) dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow x false) i [] r dr (x :: old) (digitDiff borrow x false :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_columns_right (out : Option Bool) (borrow y : Bool) (i d dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i (y :: d) [] dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow false y) i d [] (y :: dr) old (digitDiff borrow false y :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_columns_done (out : Option Bool) (borrow : Bool) (i dr old trial q : List Bool) :
    (computer out).step (cfg (some .columns) borrow i [] [] dr old trial q) =
      some (cfg (some (if borrow then .restoreBad else .restoreGood)) false i [] [] dr old trial (shiftBit (!borrow) q)) := by
  cases borrow <;> cases q <;> simp only [shiftBit] <;> simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst] <;> congr 2

/-- One bitwise subtraction pass also copies both consumed operands. -/
theorem columns_exact (out : Option Bool) (borrow : Bool) (i d r dr old trial q : List Bool) :
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

@[simp] theorem step_restore_good_both (out : Option Bool) (x y : Bool) (i d dr bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] (x :: dr) (y :: bs) fixed q) =
      some (cfg (some .restoreGood) false i (x :: d) [] dr bs fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_good_left (out : Option Bool) (x : Bool) (i d dr fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] (x :: dr) [] fixed q) =
      some (cfg (some .restoreGood) false i (x :: d) [] dr [] fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_good_right (out : Option Bool) (y : Bool) (i d bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] [] (y :: bs) fixed q) =
      some (cfg (some .restoreGood) false i d [] [] bs fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_good_nil (out : Option Bool) (i d fixed q : List Bool) :
    (computer out).step (cfg (some .restoreGood) false i d [] [] [] fixed q) =
      some (cfg (some .trimTrial) false i d [] [] [] fixed q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

/-- Restore the divisor while discarding the rejected work word. -/
theorem restore_good_exact (out : Option Bool) (i d dr bs fixed q : List Bool) :
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

@[simp] theorem step_restore_bad_both (out : Option Bool) (x y : Bool) (i d dr bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] (x :: dr) fixed (y :: bs) q) =
      some (cfg (some .restoreBad) false i (x :: d) [] dr fixed bs q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_bad_left (out : Option Bool) (x : Bool) (i d dr fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] (x :: dr) fixed [] q) =
      some (cfg (some .restoreBad) false i (x :: d) [] dr fixed [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_bad_right (out : Option Bool) (y : Bool) (i d bs fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] [] fixed (y :: bs) q) =
      some (cfg (some .restoreBad) false i d [] [] fixed bs q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

@[simp] theorem step_restore_bad_nil (out : Option Bool) (i d fixed q : List Bool) :
    (computer out).step (cfg (some .restoreBad) false i d [] [] fixed [] q) =
      some (cfg (some .reverseOld) false i d [] [] fixed [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, saveSecond, again, ifFirst]
  congr 2

/-- Restore the divisor while discarding the rejected work word. -/
theorem restore_bad_exact (out : Option Bool) (i d dr bs fixed q : List Bool) :
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

@[simp] theorem step_reverse_trial_cons (out : Option Bool) (x : Bool) (i d r w q : List Bool) :
    (computer out).step (cfg (some .reverseTrial) false i d r [] [] (x :: w) q) =
      some (cfg (some .reverseTrial) false i d (x :: r) [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_reverse_trial_nil (out : Option Bool) (i d r q : List Bool) :
    (computer out).step (cfg (some .reverseTrial) false i d r [] [] [] q) =
      some (cfg (some .root) false i d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

theorem reverse_trial_exact (out : Option Bool) (i d r w q : List Bool) :
    Runs out (cfg (some .reverseTrial) false i d r [] [] w q)
      (cfg (some .root) false i d (w.reverse ++ r) [] [] [] q) (w.length + 1) := by
  induction w generalizing r with
  | nil => simpa using Runs.one (step_reverse_trial_nil out i d r q)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_trial_cons out x i d r w q)).trans (ih (x :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_reverse_old_cons (out : Option Bool) (x : Bool) (i d r w q : List Bool) :
    (computer out).step (cfg (some .reverseOld) false i d r [] (x :: w) [] q) =
      some (cfg (some .reverseOld) false i d (x :: r) [] w [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_reverse_old_nil (out : Option Bool) (i d r q : List Bool) :
    (computer out).step (cfg (some .reverseOld) false i d r [] [] [] q) =
      some (cfg (some .root) false i d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

theorem reverse_old_exact (out : Option Bool) (i d r w q : List Bool) :
    Runs out (cfg (some .reverseOld) false i d r [] w [] q)
      (cfg (some .root) false i d (w.reverse ++ r) [] [] [] q) (w.length + 1) := by
  induction w generalizing r with
  | nil => simpa using Runs.one (step_reverse_old_nil out i d r q)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_old_cons out x i d r w q)).trans (ih (x :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_trim_false (out : Option Bool) (i d w q : List Bool) :
    (computer out).step (cfg (some .trimTrial) false i d [] [] [] (false :: w) q) =
      some (cfg (some .trimTrial) false i d [] [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_trim_true (out : Option Bool) (i d w q : List Bool) :
    (computer out).step (cfg (some .trimTrial) false i d [] [] [] (true :: w) q) =
      some (cfg (some .reverseTrial) false i d [true] [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

@[simp] theorem step_trim_nil (out : Option Bool) (i d q : List Bool) :
    (computer out).step (cfg (some .trimTrial) false i d [] [] [] [] q) =
      some (cfg (some .root) false i d [] [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, saveFirst, again]
  congr 2

/-- High zeros are explicitly popped before reversing the surviving difference. -/
theorem trim_exact (out : Option Bool) (i d w q : List Bool) :
    Runs out (cfg (some .trimTrial) false i d [] [] [] w q)
      (cfg (some .root) false i d (normalize w.reverse) [] [] [] q) (w.length + 1) := by
  induction w with
  | nil => simpa using Runs.one (step_trim_nil out i d q)
  | cons x w ih =>
    cases x with
    | false => simpa using (Runs.one (step_trim_false out i d w q)).trans ih
    | true =>
      have h := (Runs.one (step_trim_true out i d w q)).trans (reverse_trial_exact out i d [true] w q)
      simpa [List.reverse_cons, List.append_assoc] using h


/-- Most-significant-first paired bit stream supplied to the core. -/
def digitStream (ds : List Digit) : List Bool := ds.flatMap (fun d => [d.1, d.2])

@[simp] theorem digitStream_nil : digitStream [] = [] := rfl
@[simp] theorem digitStream_cons (d : Digit) (ds : List Digit) :
    digitStream (d :: ds) = d.1 :: d.2 :: digitStream ds := rfl
@[simp] theorem digitStream_append (a b : List Digit) :
    digitStream (a ++ b) = digitStream a ++ digitStream b := by simp [digitStream]
@[simp] theorem digitStream_length (ds : List Digit) : (digitStream ds).length = 2 * ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [digitStream_cons, List.length_cons, ih]; omega

/-- Exact charged cost for one paired digit and its root update. -/
def digitTime (digit : Digit) (q r : List Bool) : ℕ :=
  let shifted := trialWord digit r
  let width := max shifted.length (threshold q).length
  if (subBits false shifted (threshold q)).2 then 2 * width + shifted.length + 5
  else 3 * width + 5

/-- Complete paired-digit execution, leaving all trial and copy stacks empty. -/
theorem digit_exact (out : Option Bool) (digit : Digit) (i q r : List Bool) :
    Runs out (cfg (some .next) false (digit.1 :: digit.2 :: i) q r [] [] [] [])
      (cfg (some .next) false i (SquareRootBits.step digit q r).1
        (SquareRootBits.step digit q r).2 [] [] [] []) (digitTime digit q r) := by
  have h₁ := Runs.one (step_next_pair out digit.1 digit.2 i q r)
  have h₂ := columns_exact out false i (threshold q) (trialWord digit r) [] [] [] []
  simp only [List.append_nil] at h₂
  cases hb : (subBits false (trialWord digit r) (threshold q)).2 with
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h₂
    have h₃ := restore_good_exact out i [] (threshold q).reverse (trialWord digit r).reverse
      (subBits false (trialWord digit r) (threshold q)).1.reverse (shiftBit true [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₃
    have h₄ := trim_exact out i (threshold q)
      (subBits false (trialWord digit r) (threshold q)).1.reverse (shiftBit true [])
    simp only [List.reverse_reverse, List.length_reverse, subBits_length] at h₄
    have h₅ := Runs.one (step_root out true i q
      (normalize (subBits false (trialWord digit r) (threshold q)).1))
    have h := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
    convert h using 1 <;> simp [SquareRootBits.step, digitTime, hb, Nat.max_comm]
    all_goals omega
  | true =>
    simp only [hb, ↓reduceIte, Bool.not_true] at h₂
    have h₃ := restore_bad_exact out i [] (threshold q).reverse
      (subBits false (trialWord digit r) (threshold q)).1.reverse (trialWord digit r).reverse
      (shiftBit false [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse, subBits_length] at h₃
    have h₄ := reverse_old_exact out i (threshold q) [] (trialWord digit r).reverse (shiftBit false [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₄
    have h₅ := Runs.one (step_root out false i q (trialWord digit r))
    have h := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
    convert h using 1 <;> simp [SquareRootBits.step, digitTime, hb, Nat.max_comm]
    all_goals omega

/-- Sum of actual transition counts, with no numeric-value clock. -/
def loopTime : List Digit → List Bool → List Bool → ℕ
  | [], _, _ => 0
  | d :: ds, q, r => let next := SquareRootBits.step d q r
                     digitTime d q r + loopTime ds next.1 next.2

/-- The reusable core exposes both computed root and square remainder. -/
theorem loop_exact (out : Option Bool) (ds : List Digit) (q r : List Bool) :
    Runs out (cfg (some .next) false (digitStream ds) q r [] [] [] [])
      (cfg (some .finish) false [] (SquareRootBits.loop ds q r).1
        (SquareRootBits.loop ds q r).2 [] [] [] []) (loopTime ds q r + 1) := by
  induction ds generalizing q r with
  | nil => simpa [loopTime, SquareRootBits.loop] using Runs.one (step_next_nil out q r)
  | cons d ds ih =>
    have h := (digit_exact out d (digitStream ds) q r).trans
      (ih (SquareRootBits.step d q r).1 (SquareRootBits.step d q r).2)
    simpa [SquareRootBits.loop, loopTime, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem trialWord_length_le (d : Digit) (r : List Bool) :
    (trialWord d r).length ≤ r.length + 2 := by
  have h₁ := shiftBit_length_le d.1 r
  have h₂ := shiftBit_length_le d.2 (shiftBit d.1 r)
  change (shiftBit d.2 (shiftBit d.1 r)).length ≤ _
  omega

theorem threshold_length_le (q : List Bool) : (threshold q).length ≤ q.length + 2 := by
  have h₁ := shiftBit_length_le false q
  have h₂ := shiftBit_length_le true (shiftBit false q)
  change (shiftBit true (shiftBit false q)).length ≤ _
  omega

theorem step_max_length_le (d : Digit) (q r : List Bool) :
    max (SquareRootBits.step d q r).1.length (SquareRootBits.step d q r).2.length ≤
      max q.length r.length + 2 := by
  have hq := step_root_length_le d q r
  have hr := trialWord_length_le d r
  have ht := threshold_length_le q
  have hn := normalize_length_le (subBits false (trialWord d r) (threshold q)).1
  rw [subBits_length] at hn
  cases hb : (subBits false (trialWord d r) (threshold q)).2 <;>
    simp [SquareRootBits.step, hb] at hq ⊢ <;> omega

/-- Each digit costs linearly in the current bit lengths. -/
theorem digitTime_le (d : Digit) (q r : List Bool) :
    digitTime d q r ≤ 3 * max q.length r.length + 11 := by
  have hr := trialWord_length_le d r
  have ht := threshold_length_le q
  dsimp only [digitTime]
  split <;> omega

/-- Quadratic bit-length transition bound, including all copy/restore passes. -/
theorem loopTime_le (ds : List Digit) (q r : List Bool) :
    loopTime ds q r ≤ (3 * max q.length r.length + 6 * ds.length + 11) * ds.length := by
  induction ds generalizing q r with
  | nil => simp [loopTime]
  | cons d ds ih =>
    have hi := ih (SquareRootBits.step d q r).1 (SquareRootBits.step d q r).2
    have hs := step_max_length_le d q r
    have ht := digitTime_le d q r
    have hc :
        (3 * max (SquareRootBits.step d q r).1.length (SquareRootBits.step d q r).2.length +
          6 * ds.length + 11) * ds.length ≤
        (3 * (max q.length r.length + 2) + 6 * ds.length + 11) * ds.length :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [loopTime, List.length_cons]
    calc
      _ ≤ (3 * max q.length r.length + 11) +
          (3 * (max q.length r.length + 2) + 6 * ds.length + 11) * ds.length :=
        Nat.add_le_add ht (hi.trans hc)
      _ ≤ _ := by simp only [Nat.mul_add, Nat.add_mul]; omega

theorem loop_max_length_le (ds : List Digit) (q r : List Bool) :
    max (SquareRootBits.loop ds q r).1.length (SquareRootBits.loop ds q r).2.length ≤
      max q.length r.length + 2 * ds.length := by
  induction ds generalizing q r with
  | nil => simp [SquareRootBits.loop]
  | cons d ds ih =>
    have hi := ih (SquareRootBits.step d q r).1 (SquareRootBits.step d q r).2
    have hs := step_max_length_le d q r
    simp only [SquareRootBits.loop, List.length_cons]
    omega

/-- Preserve both canonical results for a returning caller such as unpair. -/
@[simp] theorem step_finish_both (q r : List Bool) :
    (computer none).step (cfg (some .finish) false [] q r [] [] [] []) =
      some (cfg none false [] q r [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes]
  congr 2

theorem compute_both_exact (bits : List Bool) :
    Runs none (cfg (some .next) false (digitStream (groupBits bits).reverse) [] [] [] [] [] [])
      (cfg none false [] (sqrtBits bits).1 (sqrtBits bits).2 [] [] [] [])
      (loopTime (groupBits bits).reverse [] [] + 2) := by
  have h := (loop_exact none (groupBits bits).reverse [] []).trans
    (Runs.one (step_finish_both (sqrtBits bits).1 (sqrtBits bits).2))
  convert h using 1 <;> omega

theorem compute_both_encodeNat_exact (n : ℕ) :
    Runs none (cfg (some .next) false (digitStream (groupBits (encodeNat n)).reverse) [] [] [] [] [] [])
      (cfg none false [] (encodeNat (Nat.sqrt n)) (encodeNat (n - Nat.sqrt n ^ 2)) [] [] [] [])
      (loopTime (groupBits (encodeNat n)).reverse [] [] + 2) := by
  have h := compute_both_exact (encodeNat n)
  rwa [sqrtBits_encodeNat] at h

/-- Select root or remainder, discarding the other word one bit per transition. -/
def selected (out : Bool) (qr : List Bool × List Bool) : List Bool :=
  if out then qr.2 else qr.1

def finalCfg (out : Bool) (word : List Bool) : Config :=
  cfg none false [] (if out then [] else word) (if out then word else []) [] [] [] []

@[simp] theorem step_finish_root_cons (x : Bool) (xs q : List Bool) :
    (computer (some false)).step (cfg (some .finish) false [] q (x :: xs) [] [] [] []) =
      some (cfg (some .finish) false [] q xs [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
    tapes, saveFirst, again]
  congr 2

@[simp] theorem step_finish_root_nil (q : List Bool) :
    (computer (some false)).step (cfg (some .finish) false [] q [] [] [] [] []) =
      some (finalCfg false q) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
    tapes, saveFirst, again, finalCfg]
  congr 2

@[simp] theorem step_finish_remainder_cons (x : Bool) (xs r : List Bool) :
    (computer (some true)).step (cfg (some .finish) false [] (x :: xs) r [] [] [] []) =
      some (cfg (some .finish) false [] xs r [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
    tapes, saveFirst, again]
  congr 2

@[simp] theorem step_finish_remainder_nil (r : List Bool) :
    (computer (some true)).step (cfg (some .finish) false [] [] r [] [] [] []) =
      some (finalCfg true r) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial,
    tapes, saveFirst, again, finalCfg]
  congr 2

theorem finish_root_exact (q r : List Bool) :
    Runs (some false) (cfg (some .finish) false [] q r [] [] [] []) (finalCfg false q) (r.length + 1) := by
  induction r with
  | nil => exact Runs.one (step_finish_root_nil q)
  | cons x r ih => simpa using (Runs.one (step_finish_root_cons x r q)).trans ih

theorem finish_remainder_exact (q r : List Bool) :
    Runs (some true) (cfg (some .finish) false [] q r [] [] [] []) (finalCfg true r) (q.length + 1) := by
  induction q with
  | nil => exact Runs.one (step_finish_remainder_nil r)
  | cons x q ih => simpa using (Runs.one (step_finish_remainder_cons x q r)).trans ih

theorem finish_exact (out : Bool) (q r : List Bool) :
    Runs (some out) (cfg (some .finish) false [] q r [] [] [] [])
      (finalCfg out (selected out (q, r))) ((selected (!out) (q,r)).length + 1) := by
  cases out with
  | false => simpa [selected] using finish_root_exact q r
  | true => simpa [selected] using finish_remainder_exact q r

/-- Digit processing and final clean-output cost. -/
def computeTime (out : Bool) (ds : List Digit) : ℕ :=
  loopTime ds [] [] + (selected (!out) (SquareRootBits.loop ds [] [])).length + 2

theorem compute_exact (out : Bool) (bits : List Bool) :
    Runs (some out) (cfg (some .next) false (digitStream (groupBits bits).reverse) [] [] [] [] [] [])
      (finalCfg out (selected out (sqrtBits bits))) (computeTime out (groupBits bits).reverse) := by
  have h₁ := loop_exact (some out) (groupBits bits).reverse [] []
  have h₂ := finish_exact out (sqrtBits bits).1 (sqrtBits bits).2
  have h := h₁.trans h₂
  convert h using 1 <;> simp [computeTime, sqrtBits, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

theorem compute_encodeNat_exact (out : Bool) (n : ℕ) :
    Runs (some out) (cfg (some .next) false (digitStream (groupBits (encodeNat n)).reverse) [] [] [] [] [] [])
      (finalCfg out (encodeNat (if out then n - Nat.sqrt n ^ 2 else Nat.sqrt n)))
      (computeTime out (groupBits (encodeNat n)).reverse) := by
  have h := compute_exact out (encodeNat n)
  rw [sqrtBits_encodeNat] at h
  cases out <;> simpa [selected] using h

theorem computeTime_le (out : Bool) (ds : List Digit) :
    computeTime out ds ≤ 6 * ds.length ^ 2 + 13 * ds.length + 2 := by
  have hl := loopTime_le ds [] []
  have hs := loop_max_length_le ds [] []
  simp only [List.length_nil, Nat.max_self, Nat.mul_zero, Nat.zero_add] at hl hs
  have ho : (selected (!out) (SquareRootBits.loop ds [] [])).length ≤ 2 * ds.length := by
    cases out <;> simp [selected] <;> omega
  unfold computeTime
  calc
    _ ≤ (6 * ds.length + 11) * ds.length + 2 * ds.length + 2 := by omega
    _ = _ := by ring

/-- The prepared result exactly matches the finite machine's clean halt. -/
theorem finalCfg_halt (out : Bool) (word : List Bool) :
    finalCfg out word = haltList (computer (some out)) word := by
  cases out <;> dsimp [finalCfg, cfg, haltList, computer, reset, initial]
  all_goals
    congr 1
    funext k
    cases k <;> rfl

theorem program_budget (out : Option Bool) (label : Label) : TM2Cost.budget (program out label) ≤ 17 := by
  cases out with
  | none => cases label <;> decide
  | some out => cases out <;> cases label <;> decide

@[simp] theorem stack_count (out : Bool) : Fintype.card (computer (some out)).K = 7 := by cases out <;> decide
@[simp] theorem label_count (out : Bool) : Fintype.card (computer (some out)).Λ = 9 := by cases out <;> decide
@[simp] theorem state_count (out : Bool) : Fintype.card (computer (some out)).σ = 18 := by cases out <;> decide

end Holant.Complexity.BinaryArithmetic.SquareRoot
