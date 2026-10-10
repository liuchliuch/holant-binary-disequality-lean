import Holant.Complexity.BinaryArithmetic.SubtractBits
import Holant.Complexity.BinaryArithmetic.Addition

/-!
# A finite borrow-subtractor with exact binary transition counts

The column loop reads one bit from each operand, using false for exhausted
operands. A final borrow selects a clearing loop, implementing natural-number
truncation. Otherwise a trimming loop explicitly discards high zero bits from
the reversed result before reversing the surviving bits into the output stack.
Every register, stack alphabet and program label is finite. Prepared-input
execution costs exactly twice the longer operand length plus two transitions.
-/

open Holant.Complexity Holant.Complexity.BinaryArithmetic
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Subtraction

open Turing Computability
open Turing.TM2.Stmt

abbrev Stack := Addition.Stack
abbrev State := Addition.State
abbrev initial := Addition.initial
abbrev reset := Addition.reset
abbrev tapes := Addition.tapes

inductive Label
  | columns | trim | reverse | clear
  deriving DecidableEq

instance : Fintype Label := ⟨{.columns, .trim, .reverse, .clear}, by intro k; cases k <;> simp⟩

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label State
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label State

/-- Each arithmetic instruction inspects at most three bits. -/
def program : Label → Statement
  | .columns =>
    pop .left (fun v x => (v.1, x, v.2.2))
      (pop .right (fun v y => (v.1, v.2.1, y))
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (push .work (fun v => digitDiff v.1 (v.2.1.getD false) (v.2.2.getD false))
            (load (fun v => reset (digitBorrow v.1 (v.2.1.getD false) (v.2.2.getD false)))
              (goto (fun _ => .columns))))
          (branch (fun v => v.1)
            (load (fun _ => initial) (goto (fun _ => .clear)))
            (load (fun _ => initial) (goto (fun _ => .trim))))))
  | .trim =>
    pop .work (fun v x => (v.1, x, v.2.2))
      (branch (fun v => v.2.1.isSome)
        (branch (fun v => v.2.1.getD false)
          (push .out (fun _ => true) (load (fun _ => initial) (goto (fun _ => .reverse))))
          (load (fun _ => initial) (goto (fun _ => .trim))))
        (load (fun _ => initial) halt))
  | .reverse =>
    pop .work (fun v x => (v.1, x, v.2.2))
      (branch (fun v => v.2.1.isSome)
        (push .out (fun v => v.2.1.getD false)
          (load (fun _ => initial) (goto (fun _ => .reverse))))
        (load (fun _ => initial) halt))
  | .clear =>
    pop .work (fun v x => (v.1, x, v.2.2))
      (branch (fun v => v.2.1.isSome)
        (load (fun _ => initial) (goto (fun _ => .clear)))
        (load (fun _ => initial) halt))

abbrev computer : FinTM2 where
  K := Stack
  k₀ := .left
  k₁ := .out
  Γ _ := Bool
  Λ := Label
  main := .columns
  σ := State
  initialState := initial
  m := program

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def cfg (label : Option Label) (borrow : Bool) (a b w o : List Bool) : Config :=
  ⟨label, reset borrow, tapes a b w o⟩

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

def Runs.toTimed {a b : Config} {n : ℕ} (h : Runs a b n) :
    StateTransition.EvalsToInTime computer.step a (some b) n where
  steps := n
  evals_in_steps := h
  steps_le_m := Nat.le_refl n

@[simp] theorem step_columns_both (borrow x y : Bool) (a b w o : List Bool) :
    computer.step (cfg (some .columns) borrow (x :: a) (y :: b) w o) =
      some (cfg (some .columns) (digitBorrow borrow x y) a b (digitDiff borrow x y :: w) o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_columns_left (borrow x : Bool) (a w o : List Bool) :
    computer.step (cfg (some .columns) borrow (x :: a) [] w o) =
      some (cfg (some .columns) (digitBorrow borrow x false) a [] (digitDiff borrow x false :: w) o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_columns_right (borrow y : Bool) (b w o : List Bool) :
    computer.step (cfg (some .columns) borrow [] (y :: b) w o) =
      some (cfg (some .columns) (digitBorrow borrow false y) [] b (digitDiff borrow false y :: w) o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_columns_done (borrow : Bool) (w o : List Bool) :
    computer.step (cfg (some .columns) borrow [] [] w o) =
      some (cfg (some (if borrow then .clear else .trim)) false [] [] w o) := by
  cases borrow <;>
    simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes] <;>
    congr 2

/-- One transition per input column, then one branch on the final borrow. -/
theorem columns_exact (borrow : Bool) (a b w o : List Bool) :
    Runs (cfg (some .columns) borrow a b w o)
      (cfg (some (if (subBits borrow a b).2 then .clear else .trim)) false [] []
        ((subBits borrow a b).1.reverse ++ w) o)
      (max a.length b.length + 1) := by
  induction a generalizing b borrow w with
  | nil =>
    induction b generalizing borrow w with
    | nil => simpa [subBits] using Runs.one (step_columns_done borrow w o)
    | cons y b ih =>
      have h := (Runs.one (step_columns_right borrow y b w o)).trans
        (ih (digitBorrow borrow false y) (digitDiff borrow false y :: w))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
  | cons x a ih =>
    cases b with
    | nil =>
      have h := (Runs.one (step_columns_left borrow x a w o)).trans
        (ih (digitBorrow borrow x false) [] (digitDiff borrow x false :: w))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
    | cons y b =>
      have h := (Runs.one (step_columns_both borrow x y a b w o)).trans
        (ih (digitBorrow borrow x y) b (digitDiff borrow x y :: w))
      simpa [subBits, List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_reverse_cons (x : Bool) (w o : List Bool) :
    computer.step (cfg (some .reverse) false [] [] (x :: w) o) =
      some (cfg (some .reverse) false [] [] w (x :: o)) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_reverse_nil (o : List Bool) :
    computer.step (cfg (some .reverse) false [] [] [] o) =
      some (cfg none false [] [] [] o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

theorem reverse_exact (w o : List Bool) :
    Runs (cfg (some .reverse) false [] [] w o)
      (cfg none false [] [] [] (w.reverse ++ o)) (w.length + 1) := by
  induction w generalizing o with
  | nil => simpa using Runs.one (step_reverse_nil o)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_cons x w o)).trans (ih (x :: o))
    simpa [List.reverse_cons, List.append_assoc] using h

@[simp] theorem step_trim_false (w : List Bool) :
    computer.step (cfg (some .trim) false [] [] (false :: w) []) =
      some (cfg (some .trim) false [] [] w []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_trim_true (w : List Bool) :
    computer.step (cfg (some .trim) false [] [] (true :: w) []) =
      some (cfg (some .reverse) false [] [] w [true]) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_trim_nil :
    computer.step (cfg (some .trim) false [] [] [] []) =
      some (cfg none false [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

/-- The high-zero trimming and final reversal are explicit stack loops. -/
theorem trim_exact (w : List Bool) :
    Runs (cfg (some .trim) false [] [] w [])
      (cfg none false [] [] [] (normalize w.reverse)) (w.length + 1) := by
  induction w with
  | nil => simpa [normalize] using Runs.one step_trim_nil
  | cons x w ih =>
    cases x with
    | false =>
      have h := (Runs.one (step_trim_false w)).trans ih
      simpa [normalize] using h
    | true =>
      have h := (Runs.one (step_trim_true w)).trans (reverse_exact w [true])
      simpa [normalize, List.reverse_cons] using h

@[simp] theorem step_clear_cons (x : Bool) (w : List Bool) :
    computer.step (cfg (some .clear) false [] [] (x :: w) []) =
      some (cfg (some .clear) false [] [] w []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_clear_nil :
    computer.step (cfg (some .clear) false [] [] [] []) =
      some (cfg none false [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

theorem clear_exact (w : List Bool) :
    Runs (cfg (some .clear) false [] [] w [])
      (cfg none false [] [] [] []) (w.length + 1) := by
  induction w with
  | nil => simpa using Runs.one step_clear_nil
  | cons x w ih =>
    simpa using (Runs.one (step_clear_cons x w)).trans ih

/-- Exact timing includes borrow handling, truncation, normalization and cleanup. -/
theorem compute_exact (a b : List Bool) :
    Runs (cfg (some .columns) false a b [] [])
      (cfg none false [] [] [] (subNatBits a b)) (2 * max a.length b.length + 2) := by
  have hc := columns_exact false a b [] []
  simp only [List.append_nil] at hc
  cases hborrow : (subBits false a b).2 with
  | false =>
    simp only [hborrow, Bool.false_eq_true, ↓reduceIte] at hc
    have h := hc.trans (trim_exact (subBits false a b).1.reverse)
    simpa [subNatBits, hborrow, subBits_length, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  | true =>
    simp only [hborrow, ↓reduceIte] at hc
    have h := hc.trans (clear_exact (subBits false a b).1.reverse)
    simpa [subNatBits, hborrow, subBits_length, Nat.two_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

theorem compute_encodeNat_exact (a b : ℕ) :
    Runs (cfg (some .columns) false (encodeNat a) (encodeNat b) [] [])
      (cfg none false [] [] [] (encodeNat (a - b)))
      (2 * max (encodeNat a).length (encodeNat b).length + 2) := by
  simpa only [subNatBits_encodeNat] using compute_exact (encodeNat a) (encodeNat b)

/-- The finite straight-line syntax has a constant primitive instruction budget. -/
theorem program_budget (label : Label) : TM2Cost.budget (program label) ≤ 7 := by
  cases label <;> decide

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Subtraction
