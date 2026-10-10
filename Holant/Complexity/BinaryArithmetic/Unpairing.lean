import Holant.Complexity.BinaryArithmetic.SquareRoot
import Holant.Complexity.BinaryArithmetic.PairingBits
import Holant.Complexity.BinaryArithmetic.EncodedAddition
import Holant.Complexity.MachineReturn

/-! Inverse square-shell pairing by one restoring square root and its computed
square remainder, followed by one binary trial subtraction and serialization. -/

namespace Holant.Complexity.BinaryArithmetic.Unpairing
open Turing Computability
open Turing.TM2.Stmt
open DivisionBits SquareRootBits

inductive OuterLabel
  | parse | columns | restoreGood | restoreBad | trimTrial | reverseTrial | reverseOld
  | choose | outputQ | outputR | frameQ | frameR
  deriving DecidableEq
instance : Fintype OuterLabel :=
  ⟨{.parse, .columns, .restoreGood, .restoreBad, .trimTrial, .reverseTrial, .reverseOld,
    .choose, .outputQ, .outputR, .frameQ, .frameR}, by intro k; cases k <;> simp⟩

abbrev Stack := SquareRoot.Stack ⊕ Unit
abbrev Label := SquareRoot.Label ⊕ OuterLabel
abbrev Memory := SquareRoot.State × Unit
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Memory

def initial : Memory := (SquareRoot.initial, ())
def reset (b : Bool) : Memory := (SquareRoot.reset b, ())
def saveFirst (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), ())
def saveSecond (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, v.1.2.1, bit), ())
def again (label : OuterLabel) : Statement := load (fun _ => initial) (goto (fun _ => .inr label))
def ifFirst (stack : SquareRoot.Stack) (cont : Statement) : Statement :=
  branch (fun v => v.1.2.1.isSome) (push (.inl stack) (fun v => v.1.2.1.getD false) cont) cont

def returnLabel (_ : Unit) : OuterLabel := .columns

def outside : OuterLabel → Statement
  | .parse => pop (.inr ()) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (pop (.inr ()) saveSecond
          (push (.inl .input) (fun v => v.1.2.1.getD false)
            (push (.inl .input) (fun v => v.1.2.2.getD false) (again .parse))))
        (load (fun _ => initial) (goto (fun _ => .inl .next))))
  | .columns => pop (.inl .remainder) saveFirst
      (pop (.inl .divisor) saveSecond
        (branch (fun v => v.1.2.1.isSome || v.1.2.2.isSome)
          (push (.inl .trialRev) (fun v => digitDiff v.1.1 (v.1.2.1.getD false) (v.1.2.2.getD false))
            (ifFirst .oldRev
              (branch (fun v => v.1.2.2.isSome)
                (push (.inl .divisorRev) (fun v => v.1.2.2.getD false)
                  (load (fun v => reset (digitBorrow v.1.1 (v.1.2.1.getD false) (v.1.2.2.getD false)))
                    (goto (fun _ => .inr .columns))))
                (load (fun v => reset (digitBorrow v.1.1 (v.1.2.1.getD false) (v.1.2.2.getD false)))
                  (goto (fun _ => .inr .columns))))))
          (branch (fun v => v.1.1)
            (peek (.inl .quotient) saveFirst
              (branch (fun v => v.1.2.1.isSome)
                (push (.inl .quotient) (fun _ => false) (again .restoreBad))
                (again .restoreBad)))
            (push (.inl .quotient) (fun _ => true) (again .restoreGood)))))
  | .restoreGood => pop (.inl .divisorRev) saveFirst
      (pop (.inl .oldRev) saveSecond
        (branch (fun v => v.1.2.1.isSome || v.1.2.2.isSome)
          (ifFirst .divisor (again .restoreGood)) (again .trimTrial)))
  | .restoreBad => pop (.inl .divisorRev) saveFirst
      (pop (.inl .trialRev) saveSecond
        (branch (fun v => v.1.2.1.isSome || v.1.2.2.isSome)
          (ifFirst .divisor (again .restoreBad)) (again .reverseOld)))
  | .trimTrial => pop (.inl .trialRev) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (branch (fun v => v.1.2.1.getD false)
          (push (.inl .remainder) (fun _ => true) (again .reverseTrial))
          (again .trimTrial))
        (again .choose))
  | .reverseTrial => pop (.inl .trialRev) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .remainder) (fun v => v.1.2.1.getD false) (again .reverseTrial))
        (again .choose))
  | .reverseOld => pop (.inl .oldRev) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .remainder) (fun v => v.1.2.1.getD false) (again .reverseOld))
        (again .choose))
  | .choose => pop (.inl .quotient) saveFirst
      (branch (fun v => v.1.2.1.isSome) (again .outputR) (again .outputQ))
  | .outputQ => pop (.inl .divisor) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr ()) (fun v => v.1.2.1.getD false) (again .outputQ))
        (push (.inr ()) (fun _ => false) (again .frameR)))
  | .outputR => pop (.inl .remainder) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr ()) (fun v => v.1.2.1.getD false) (again .outputR))
        (push (.inr ()) (fun _ => false) (again .frameQ)))
  | .frameQ => pop (.inl .divisor) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr ()) (fun v => v.1.2.1.getD false)
          (push (.inr ()) (fun _ => true) (again .frameQ)))
        (load (fun _ => initial) halt))
  | .frameR => pop (.inl .remainder) saveFirst
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr ()) (fun v => v.1.2.1.getD false)
          (push (.inr ()) (fun _ => true) (again .frameR)))
        (load (fun _ => initial) halt))

abbrev computer : FinTM2 where
  K := Stack
  k₀ := .inr ()
  k₁ := .inr ()
  Γ _ := Bool
  Λ := Label
  main := .inr .parse
  σ := Memory
  initialState := initial
  m := MachineReturn.program returnLabel (SquareRoot.program none) outside

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def cfg (label : Option OuterLabel) (borrow : Bool) (i d r dr old trial q : List Bool) : Config :=
  ⟨label.map Sum.inr, reset borrow,
    Sum.elim (SquareRoot.tapes i d r dr old trial q) (fun _ => [])⟩

def outputCfg (label : Option OuterLabel) (q r word : List Bool) : Config :=
  ⟨label.map Sum.inr, initial, Sum.elim (SquareRoot.tapes [] q r [] [] [] []) (fun _ => word)⟩

def parserCfg (word i : List Bool) : Config :=
  ⟨some (.inr .parse), initial, Sum.elim (SquareRoot.tapes i [] [] [] [] [] []) (fun _ => word)⟩

def sqrtCfg (c : SquareRoot.Config) : Config := MachineReturn.cfg returnLabel c () (fun _ : Unit => [])

@[simp] theorem update_word (source : SquareRoot.Stack → List Bool) (word next : List Bool) :
    Function.update (Sum.elim source (fun _ : Unit => word)) (.inr ()) next =
      Sum.elim source (fun _ : Unit => next) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k; simp

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

@[simp] theorem step_columns_both (borrow x y : Bool) (i d r dr old trial q : List Bool) :
    computer.step (cfg (some .columns) borrow i (y :: d) (x :: r) dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow x y) i d r (y :: dr) (x :: old) (digitDiff borrow x y :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_columns_left (borrow x : Bool) (i r dr old trial q : List Bool) :
    computer.step (cfg (some .columns) borrow i [] (x :: r) dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow x false) i [] r dr (x :: old) (digitDiff borrow x false :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_columns_right (borrow y : Bool) (i d dr old trial q : List Bool) :
    computer.step (cfg (some .columns) borrow i (y :: d) [] dr old trial q) =
      some (cfg (some .columns) (digitBorrow borrow false y) i d [] (y :: dr) old (digitDiff borrow false y :: trial) q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_columns_done (borrow : Bool) (i dr old trial q : List Bool) :
    computer.step (cfg (some .columns) borrow i [] [] dr old trial q) =
      some (cfg (some (if borrow then .restoreBad else .restoreGood)) false i [] [] dr old trial (shiftBit (!borrow) q)) := by
  cases borrow <;> cases q <;> simp only [shiftBit] <;> simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr] <;> congr 2

/-- One bitwise subtraction pass also copies both consumed operands. -/
theorem columns_exact (borrow : Bool) (i d r dr old trial q : List Bool) :
    Runs (cfg (some .columns) borrow i d r dr old trial q)
      (cfg (some (if (subBits borrow r d).2 then .restoreBad else .restoreGood)) false
        i [] [] (d.reverse ++ dr) (r.reverse ++ old)
        ((subBits borrow r d).1.reverse ++ trial) (shiftBit (!(subBits borrow r d).2) q))
      (max r.length d.length + 1) := by
  induction r generalizing d borrow dr old trial with
  | nil =>
    induction d generalizing borrow dr trial with
    | nil => simpa [subBits] using Runs.one (step_columns_done borrow i dr old trial q)
    | cons y d ih =>
      have h := (Runs.one (step_columns_right borrow y i d dr old trial q)).trans
        (ih (digitBorrow borrow false y) (y :: dr) (digitDiff borrow false y :: trial))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
  | cons x r ih =>
    cases d with
    | nil =>
      have h := (Runs.one (step_columns_left borrow x i r dr old trial q)).trans
        (ih (digitBorrow borrow x false) [] dr (x :: old) (digitDiff borrow x false :: trial))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
    | cons y d =>
      have h := (Runs.one (step_columns_both borrow x y i d r dr old trial q)).trans
        (ih (digitBorrow borrow x y) d (y :: dr) (x :: old) (digitDiff borrow x y :: trial))
      simpa [subBits, List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_restore_good_both (x y : Bool) (i d dr bs fixed q : List Bool) :
    computer.step (cfg (some .restoreGood) false i d [] (x :: dr) (y :: bs) fixed q) =
      some (cfg (some .restoreGood) false i (x :: d) [] dr bs fixed q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_good_left (x : Bool) (i d dr fixed q : List Bool) :
    computer.step (cfg (some .restoreGood) false i d [] (x :: dr) [] fixed q) =
      some (cfg (some .restoreGood) false i (x :: d) [] dr [] fixed q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_good_right (y : Bool) (i d bs fixed q : List Bool) :
    computer.step (cfg (some .restoreGood) false i d [] [] (y :: bs) fixed q) =
      some (cfg (some .restoreGood) false i d [] [] bs fixed q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_good_nil (i d fixed q : List Bool) :
    computer.step (cfg (some .restoreGood) false i d [] [] [] fixed q) =
      some (cfg (some .trimTrial) false i d [] [] [] fixed q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

/-- Restore the divisor while discarding the rejected work word. -/
theorem restore_good_exact (i d dr bs fixed q : List Bool) :
    Runs (cfg (some .restoreGood) false i d [] dr bs fixed q)
      (cfg (some .trimTrial) false i (dr.reverse ++ d) [] [] [] fixed q)
      (max dr.length bs.length + 1) := by
  induction dr generalizing bs d with
  | nil =>
    induction bs with
    | nil => simpa using Runs.one (step_restore_good_nil i d fixed q)
    | cons y bs ih =>
      have h := (Runs.one (step_restore_good_right y i d bs fixed q)).trans ih
      simpa using h
  | cons x dr ih =>
    cases bs with
    | nil =>
      have h := (Runs.one (step_restore_good_left x i d dr fixed q)).trans (ih (x :: d) [])
      simpa [List.reverse_cons, List.append_assoc] using h
    | cons y bs =>
      have h := (Runs.one (step_restore_good_both x y i d dr bs fixed q)).trans (ih (x :: d) bs)
      simpa [List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_restore_bad_both (x y : Bool) (i d dr bs fixed q : List Bool) :
    computer.step (cfg (some .restoreBad) false i d [] (x :: dr) fixed (y :: bs) q) =
      some (cfg (some .restoreBad) false i (x :: d) [] dr fixed bs q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_bad_left (x : Bool) (i d dr fixed q : List Bool) :
    computer.step (cfg (some .restoreBad) false i d [] (x :: dr) fixed [] q) =
      some (cfg (some .restoreBad) false i (x :: d) [] dr fixed [] q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_bad_right (y : Bool) (i d bs fixed q : List Bool) :
    computer.step (cfg (some .restoreBad) false i d [] [] fixed (y :: bs) q) =
      some (cfg (some .restoreBad) false i d [] [] fixed bs q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_restore_bad_nil (i d fixed q : List Bool) :
    computer.step (cfg (some .restoreBad) false i d [] [] fixed [] q) =
      some (cfg (some .reverseOld) false i d [] [] fixed [] q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, saveSecond, again, ifFirst, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

/-- Restore the divisor while discarding the rejected work word. -/
theorem restore_bad_exact (i d dr bs fixed q : List Bool) :
    Runs (cfg (some .restoreBad) false i d [] dr fixed bs q)
      (cfg (some .reverseOld) false i (dr.reverse ++ d) [] [] fixed [] q)
      (max dr.length bs.length + 1) := by
  induction dr generalizing bs d with
  | nil =>
    induction bs with
    | nil => simpa using Runs.one (step_restore_bad_nil i d fixed q)
    | cons y bs ih =>
      have h := (Runs.one (step_restore_bad_right y i d bs fixed q)).trans ih
      simpa using h
  | cons x dr ih =>
    cases bs with
    | nil =>
      have h := (Runs.one (step_restore_bad_left x i d dr fixed q)).trans (ih (x :: d) [])
      simpa [List.reverse_cons, List.append_assoc] using h
    | cons y bs =>
      have h := (Runs.one (step_restore_bad_both x y i d dr bs fixed q)).trans (ih (x :: d) bs)
      simpa [List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_reverse_trial_cons (x : Bool) (i d r w q : List Bool) :
    computer.step (cfg (some .reverseTrial) false i d r [] [] (x :: w) q) =
      some (cfg (some .reverseTrial) false i d (x :: r) [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_reverse_trial_nil (i d r q : List Bool) :
    computer.step (cfg (some .reverseTrial) false i d r [] [] [] q) =
      some (cfg (some .choose) false i d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem reverse_trial_exact (i d r w q : List Bool) :
    Runs (cfg (some .reverseTrial) false i d r [] [] w q)
      (cfg (some .choose) false i d (w.reverse ++ r) [] [] [] q) (w.length + 1) := by
  induction w generalizing r with
  | nil => simpa using Runs.one (step_reverse_trial_nil i d r q)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_trial_cons x i d r w q)).trans (ih (x :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_reverse_old_cons (x : Bool) (i d r w q : List Bool) :
    computer.step (cfg (some .reverseOld) false i d r [] (x :: w) [] q) =
      some (cfg (some .reverseOld) false i d (x :: r) [] w [] q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_reverse_old_nil (i d r q : List Bool) :
    computer.step (cfg (some .reverseOld) false i d r [] [] [] q) =
      some (cfg (some .choose) false i d r [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem reverse_old_exact (i d r w q : List Bool) :
    Runs (cfg (some .reverseOld) false i d r [] w [] q)
      (cfg (some .choose) false i d (w.reverse ++ r) [] [] [] q) (w.length + 1) := by
  induction w generalizing r with
  | nil => simpa using Runs.one (step_reverse_old_nil i d r q)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_old_cons x i d r w q)).trans (ih (x :: r))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_trim_false (i d w q : List Bool) :
    computer.step (cfg (some .trimTrial) false i d [] [] [] (false :: w) q) =
      some (cfg (some .trimTrial) false i d [] [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_trim_true (i d w q : List Bool) :
    computer.step (cfg (some .trimTrial) false i d [] [] [] (true :: w) q) =
      some (cfg (some .reverseTrial) false i d [true] [] [] w q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_trim_nil (i d q : List Bool) :
    computer.step (cfg (some .trimTrial) false i d [] [] [] [] q) =
      some (cfg (some .choose) false i d [] [] [] [] q) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

/-- High zeros are explicitly popped before reversing the surviving difference. -/
theorem trim_exact (i d w q : List Bool) :
    Runs (cfg (some .trimTrial) false i d [] [] [] w q)
      (cfg (some .choose) false i d (normalize w.reverse) [] [] [] q) (w.length + 1) := by
  induction w with
  | nil => simpa using Runs.one (step_trim_nil i d q)
  | cons x w ih =>
    cases x with
    | false => simpa using (Runs.one (step_trim_false i d w q)).trans ih
    | true =>
      have h := (Runs.one (step_trim_true i d w q)).trans (reverse_trial_exact i d [true] w q)
      simpa [List.reverse_cons, List.append_assoc] using h


/-- The square-shell branch compares the already computed remainder with root. -/
def rejected (q r : List Bool) : Bool := (subBits false r q).2

def residual (q r : List Bool) : List Bool :=
  if rejected q r then r else normalize (subBits false r q).1

def trialTime (q r : List Bool) : ℕ :=
  let width := max r.length q.length
  if rejected q r then 2 * width + r.length + 3 else 3 * width + 3

/-- A single trial subtraction preserves root, selects the square-shell residual,
and keeps its one-bit branch indicator until output order is selected. -/
theorem trial_exact (q r : List Bool) :
    Runs (cfg (some .columns) false [] q r [] [] [] [])
      (cfg (some .choose) false [] q (residual q r) [] [] [] (shiftBit (!(rejected q r)) []))
      (trialTime q r) := by
  have h₁ := columns_exact false [] q r [] [] [] []
  simp only [List.append_nil] at h₁
  cases hb : (subBits false r q).2 with
  | false =>
    simp only [hb, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h₁
    have h₂ := restore_good_exact [] [] q.reverse r.reverse
      (subBits false r q).1.reverse (shiftBit true [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₂
    have h₃ := trim_exact [] q (subBits false r q).1.reverse (shiftBit true [])
    simp only [List.reverse_reverse, List.length_reverse, subBits_length] at h₃
    have h := (h₁.trans h₂).trans h₃
    convert h using 1 <;> simp [residual, rejected, trialTime, hb, Nat.max_comm] <;> omega
  | true =>
    simp only [hb, ↓reduceIte, Bool.not_true] at h₁
    have h₂ := restore_bad_exact [] [] q.reverse (subBits false r q).1.reverse r.reverse (shiftBit false [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse, subBits_length] at h₂
    have h₃ := reverse_old_exact [] q [] r.reverse (shiftBit false [])
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h₃
    have h := (h₁.trans h₂).trans h₃
    convert h using 1 <;> simp [residual, rejected, trialTime, hb, Nat.max_comm] <;> omega

@[simp] theorem step_choose_good (q r : List Bool) :
    computer.step (cfg (some .choose) false [] q r [] [] [] [true]) =
      some (outputCfg (some .outputR) q r []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, outputCfg,
    TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_choose_bad (q r : List Bool) :
    computer.step (cfg (some .choose) false [] q r [] [] [] []) =
      some (outputCfg (some .outputQ) q r []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, outputCfg,
    TM2.stepAux, reset, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_outputQ_cons (x : Bool) (xs r word : List Bool) :
    computer.step (outputCfg (some .outputQ) (x :: xs) r word) =
      some (outputCfg (some .outputQ) xs r (x :: word)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_outputQ_nil (r word : List Bool) :
    computer.step (outputCfg (some .outputQ) [] r word) =
      some (outputCfg (some .frameR) [] r (false :: word)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_frameQ_cons (x : Bool) (xs r word : List Bool) :
    computer.step (outputCfg (some .frameQ) (x :: xs) r word) =
      some (outputCfg (some .frameQ) xs r (true :: x :: word)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_frameQ_nil (word : List Bool) :
    computer.step (outputCfg (some .frameQ) [] [] word) =
      some (outputCfg none [] [] word) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_outputR_cons (x : Bool) (xs q word : List Bool) :
    computer.step (outputCfg (some .outputR) q (x :: xs) word) =
      some (outputCfg (some .outputR) q xs (x :: word)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_outputR_nil (q word : List Bool) :
    computer.step (outputCfg (some .outputR) q [] word) =
      some (outputCfg (some .frameQ) q [] (false :: word)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_frameR_cons (x : Bool) (xs q word : List Bool) :
    computer.step (outputCfg (some .frameR) q (x :: xs) word) =
      some (outputCfg (some .frameR) q xs (true :: x :: word)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_frameR_nil (word : List Bool) :
    computer.step (outputCfg (some .frameR) [] [] word) =
      some (outputCfg none [] [] word) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, outputCfg,
    TM2.stepAux, initial, SquareRoot.tapes, saveFirst, again, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem outputQ_exact (q r word : List Bool) :
    Runs (outputCfg (some .outputQ) q r word)
      (outputCfg (some .frameR) [] r (false :: (q.reverse ++ word))) (q.length + 1) := by
  induction q generalizing word with
  | nil => simpa using Runs.one (step_outputQ_nil r word)
  | cons x q ih =>
    have h := (Runs.one (step_outputQ_cons x q r word)).trans (ih (x :: word))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem outputR_exact (q r word : List Bool) :
    Runs (outputCfg (some .outputR) q r word)
      (outputCfg (some .frameQ) q [] (false :: (r.reverse ++ word))) (r.length + 1) := by
  induction r generalizing word with
  | nil => simpa using Runs.one (step_outputR_nil q word)
  | cons x r ih =>
    have h := (Runs.one (step_outputR_cons x r q word)).trans (ih (x :: word))
    simpa [List.reverse_cons, List.append_assoc] using h

def framePrefix (bits : List Bool) : List Bool := bits.flatMap (fun b => [true, b])

@[simp] theorem framePrefix_append (a b : List Bool) :
    framePrefix (a ++ b) = framePrefix a ++ framePrefix b := by simp [framePrefix]

@[simp] theorem framePrefix_nil : framePrefix [] = [] := rfl
@[simp] theorem framePrefix_singleton (b : Bool) : framePrefix [b] = [true, b] := rfl

theorem frame_eq_prefix (bits : List Bool) :
    Holant.Algebraic.frame bits = framePrefix bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [Holant.Algebraic.frame, framePrefix, ih]

theorem frameQ_exact (q word : List Bool) :
    Runs (outputCfg (some .frameQ) q [] word)
      (outputCfg none [] [] (framePrefix q.reverse ++ word)) (q.length + 1) := by
  induction q generalizing word with
  | nil => simpa using Runs.one (step_frameQ_nil word)
  | cons x q ih =>
    have h := (Runs.one (step_frameQ_cons x q [] word)).trans (ih (true :: x :: word))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem frameR_exact (r word : List Bool) :
    Runs (outputCfg (some .frameR) [] r word)
      (outputCfg none [] [] (framePrefix r.reverse ++ word)) (r.length + 1) := by
  induction r generalizing word with
  | nil => simpa using Runs.one (step_frameR_nil word)
  | cons x r ih =>
    have h := (Runs.one (step_frameR_cons x r [] word)).trans (ih (true :: x :: word))
    simpa [List.reverse_cons, List.append_assoc] using h

def pairWord (p : List Bool × List Bool) : List Bool :=
  Holant.Algebraic.frame p.1.reverse ++ p.2.reverse

def branchResult (q r : List Bool) : List Bool × List Bool :=
  if rejected q r then (residual q r, q) else (q, residual q r)

/-- Both square-shell branches serialize to the established faithful pair codec. -/
theorem serialize_exact (q r : List Bool) :
    Runs (cfg (some .choose) false [] q (residual q r) [] [] [] (shiftBit (!(rejected q r)) []))
      (outputCfg none [] [] (pairWord (branchResult q r)))
      (q.length + (residual q r).length + 3) := by
  cases hb : rejected q r with
  | false =>
    have h₁ := Runs.one (step_choose_good q (residual q r))
    have h₂ := outputR_exact q (residual q r) []
    simp only [List.append_nil] at h₂
    have h₃ := frameQ_exact q (false :: (residual q r).reverse)
    have h := (h₁.trans h₂).trans h₃
    convert h using 1 <;> try simp [branchResult, pairWord, hb, shiftBit, frame_eq_prefix, List.append_assoc]
    all_goals omega
  | true =>
    have h₁ := Runs.one (step_choose_bad q (residual q r))
    have h₂ := outputQ_exact q (residual q r) []
    simp only [List.append_nil] at h₂
    have h₃ := frameR_exact (residual q r) (false :: q.reverse)
    have h := (h₁.trans h₂).trans h₃
    convert h using 1 <;> try simp [branchResult, pairWord, hb, shiftBit, frame_eq_prefix, List.append_assoc]
    all_goals omega

def shellTime (q r : List Bool) : ℕ := trialTime q r + q.length + (residual q r).length + 3

theorem shell_exact (q r : List Bool) :
    Runs (cfg (some .columns) false [] q r [] [] [] [])
      (outputCfg none [] [] (pairWord (branchResult q r))) (shellTime q r) := by
  have h := (trial_exact q r).trans (serialize_exact q r)
  convert h using 1 <;> dsimp [shellTime] <;> omega

theorem shellTime_le (q r : List Bool) :
    shellTime q r ≤ 5 * max q.length r.length + 6 := by
  have hn := normalize_length_le (subBits false r q).1
  rw [subBits_length] at hn
  unfold shellTime trialTime residual
  cases hb : rejected q r <;> simp only [hb, ↓reduceIte, Bool.false_eq_true] <;> omega
@[simp] theorem step_pair (lo hi : Bool) (rest i : List Bool) :
    computer.step (parserCfg (lo :: hi :: rest) i) =
      some (parserCfg rest (hi :: lo :: i)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, parserCfg, outside,
    TM2.stepAux, saveFirst, saveSecond, initial, again, SquareRoot.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_single (lo : Bool) (i : List Bool) :
    computer.step (parserCfg [lo] i) = some (parserCfg [] (false :: lo :: i)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, parserCfg, outside,
    TM2.stepAux, saveFirst, saveSecond, initial, again, SquareRoot.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_nil (i : List Bool) :
    computer.step (parserCfg [] i) =
      some (sqrtCfg (SquareRoot.cfg (some .next) false i [] [] [] [] [] [])) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, parserCfg, outside,
    TM2.stepAux, saveFirst, saveSecond, initial, SquareRoot.initial, sqrtCfg, MachineReturn.cfg,
    SquareRoot.cfg, SquareRoot.reset, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

/-- Explicit bit pairing and digit reversal from the actual binary input. -/
theorem parser_exact (word i : List Bool) :
    Runs (parserCfg word i)
      (sqrtCfg (SquareRoot.cfg (some .next) false
        (SquareRoot.digitStream (groupBits word).reverse ++ i) [] [] [] [] [] []))
      ((groupBits word).length + 1) := by
  induction word using groupBits.induct generalizing i with
  | case1 => simpa [groupBits] using Runs.one (step_nil i)
  | case2 lo =>
    have h := (Runs.one (step_single lo i)).trans (Runs.one (step_nil (false :: lo :: i)))
    simpa [groupBits, SquareRoot.digitStream] using h
  | case3 lo hi rest ih =>
    have h := (Runs.one (step_pair lo hi rest i)).trans (ih (hi :: lo :: i))
    simpa [groupBits, List.reverse_cons, List.append_assoc] using h


/-- The returning sqrt subroutine preserves BOTH computed words and all costs. -/
theorem lift_sqrt {a b : SquareRoot.Config} {time : ℕ} (h : SquareRoot.Runs none a b time) :
    Runs (sqrtCfg a) (sqrtCfg b) time := by
  exact MachineReturn.run_program returnLabel (SquareRoot.program none) outside a ()
    (fun _ : Unit => []) time b h

@[simp] theorem sqrtCfg_return (q r : List Bool) :
    sqrtCfg (SquareRoot.cfg none false [] q r [] [] [] []) =
      cfg (some .columns) false [] q r [] [] [] [] := rfl

@[simp] theorem parserCfg_init (word : List Bool) : parserCfg word [] = initList computer word := by
  dsimp [parserCfg, initList, initial, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

@[simp] theorem outputCfg_halt (word : List Bool) : outputCfg none [] [] word = haltList computer word := by
  dsimp [outputCfg, haltList, initial, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

/-- All parsing, root processing, shell comparison and serialization transitions. -/
def computeTime (word : List Bool) : ℕ :=
  (groupBits word).length + 1 + SquareRoot.loopTime (groupBits word).reverse [] [] + 2 +
    shellTime (sqrtBits word).1 (sqrtBits word).2

/-- Actual machine execution agrees with the bitwise codec inverse. -/
theorem compute_exact (word : List Bool) :
    Runs (initList computer word) (haltList computer (pairWord (PairingBits.unpairBits word)))
      (computeTime word) := by
  have h₁ := parser_exact word []
  simp only [List.append_nil, parserCfg_init] at h₁
  have h₂ := lift_sqrt (SquareRoot.compute_both_exact word)
  rw [sqrtCfg_return] at h₂
  have h₃ := shell_exact (sqrtBits word).1 (sqrtBits word).2
  rw [outputCfg_halt] at h₃
  have h := (h₁.trans h₂).trans h₃
  have hb : branchResult (sqrtBits word).1 (sqrtBits word).2 = PairingBits.unpairBits word := by
    dsimp [branchResult, residual, rejected, PairingBits.unpairBits]
    split <;> simp_all
  rw [hb] at h
  convert h using 1 <;> dsimp [computeTime] <;> omega

theorem groupBits_length_le (bits : List Bool) : (groupBits bits).length ≤ bits.length := by
  induction bits using groupBits.induct with
  | case1 => simp [groupBits]
  | case2 lo => simp [groupBits]
  | case3 lo hi rest ih => simp only [groupBits, List.length_cons]; omega

/-- Entire inverse machine is bounded by a quadratic in actual input bit length. -/
theorem computeTime_le (word : List Bool) :
    computeTime word ≤ 6 * word.length ^ 2 + 22 * word.length + 9 := by
  have hl := SquareRoot.loopTime_le (groupBits word).reverse [] []
  have hs := SquareRoot.loop_max_length_le (groupBits word).reverse [] []
  have ht := shellTime_le (sqrtBits word).1 (sqrtBits word).2
  simp only [List.length_nil, Nat.max_self, Nat.mul_zero, Nat.zero_add, List.length_reverse] at hl hs
  change max (sqrtBits word).1.length (sqrtBits word).2.length ≤ 2 * (groupBits word).length at hs
  have hg := groupBits_length_le word
  have hp := Nat.pow_le_pow_left hg 2
  unfold computeTime
  nlinarith

theorem outside_budget (label : OuterLabel) : TM2Cost.budget (outside label) ≤ 12 := by
  cases label <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 17 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineReturn.program, MachineReturn.budget_stmt] using
      SquareRoot.program_budget none label
  | inr label => exact (outside_budget label).trans (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 8 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 21 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.Unpairing
