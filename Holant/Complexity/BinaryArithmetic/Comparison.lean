import Holant.Complexity.BinaryArithmetic.SubtractBits
import Holant.Complexity.BinaryArithmetic.Addition

/-!
# A finite bitwise strict comparison machine

The same binary borrow recurrence decides strict inequality without constructing
the difference. The machine consumes both operand streams and writes exactly one
Boolean symbol, using only a borrow and two optional-bit registers. Its exact
prepared-input transition count is the longer word length plus one.
-/

namespace Holant.Complexity.BinaryArithmetic.Comparison

open Turing Computability
open Turing.TM2.Stmt

abbrev Stack := Addition.Stack
abbrev State := Addition.State
abbrev initial := Addition.initial
abbrev reset := Addition.reset
abbrev tapes := Addition.tapes
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Unit State
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Unit State

/-- A single Boolean answer has a faithful one-symbol encoding. -/
def boolEncoding : Encoding Bool Bool where
  encode b := [b]
  decode := List.head?
  decode_encode _ := rfl

def program (_ : Unit) : Statement :=
  pop .left (fun v x => (v.1, x, v.2.2))
    (pop .right (fun v y => (v.1, v.2.1, y))
      (branch (fun v => v.2.1.isSome || v.2.2.isSome)
        (load (fun v => reset (digitBorrow v.1 (v.2.1.getD false) (v.2.2.getD false)))
          (goto (fun _ => ())))
        (push .out (fun v => v.1) (load (fun _ => initial) halt))))

abbrev computer : FinTM2 where
  K := Stack
  k₀ := .left
  k₁ := .out
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := State
  initialState := initial
  m := program

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def cfg (label : Option Unit) (borrow : Bool) (a b o : List Bool) : Config :=
  ⟨label, reset borrow, tapes a b [] o⟩

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

@[simp] theorem step_both (borrow x y : Bool) (a b o : List Bool) :
    computer.step (cfg (some ()) borrow (x :: a) (y :: b) o) =
      some (cfg (some ()) (digitBorrow borrow x y) a b o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_left (borrow x : Bool) (a o : List Bool) :
    computer.step (cfg (some ()) borrow (x :: a) [] o) =
      some (cfg (some ()) (digitBorrow borrow x false) a [] o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_right (borrow y : Bool) (b o : List Bool) :
    computer.step (cfg (some ()) borrow [] (y :: b) o) =
      some (cfg (some ()) (digitBorrow borrow false y) [] b o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes, Addition.tapes]
  congr 2

@[simp] theorem step_done (borrow : Bool) (o : List Bool) :
    computer.step (cfg (some ()) borrow [] [] o) =
      some (cfg none false [] [] (borrow :: o)) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes, Addition.tapes]
  congr 2

/-- The operational result is the final borrow of the binary recurrence. -/
theorem compute_exact (borrow : Bool) (a b o : List Bool) :
    Runs (cfg (some ()) borrow a b o)
      (cfg none false [] [] ((subBits borrow a b).2 :: o))
      (max a.length b.length + 1) := by
  induction a generalizing b borrow with
  | nil =>
    induction b generalizing borrow with
    | nil => simpa [subBits] using Runs.one (step_done borrow o)
    | cons y b ih =>
      have h := (Runs.one (step_right borrow y b o)).trans (ih (digitBorrow borrow false y))
      simpa [subBits] using h
  | cons x a ih =>
    cases b with
    | nil =>
      have h := (Runs.one (step_left borrow x a o)).trans (ih (digitBorrow borrow x false) [])
      simpa [subBits] using h
    | cons y b =>
      have h := (Runs.one (step_both borrow x y a b o)).trans (ih (digitBorrow borrow x y) b)
      simpa [subBits, Nat.succ_max_succ] using h

@[simp] theorem borrow_encodeNat (a b : ℕ) :
    (subBits false (encodeNat a) (encodeNat b)).2 = decide (a < b) := by
  have h := subBits_borrow_iff false (encodeNat a) (encodeNat b)
  simp only [value_encodeNat, Bool.toNat_false, Nat.add_zero] at h
  cases hb : (subBits false (encodeNat a) (encodeNat b)).2 <;> simp_all

theorem compute_encodeNat_exact (a b : ℕ) :
    Runs (cfg (some ()) false (encodeNat a) (encodeNat b) [])
      (cfg none false [] [] [decide (a < b)])
      (max (encodeNat a).length (encodeNat b).length + 1) := by
  simpa only [borrow_encodeNat] using compute_exact false (encodeNat a) (encodeNat b) []

theorem program_budget (label : Unit) : TM2Cost.budget (program label) = 6 := rfl

end Holant.Complexity.BinaryArithmetic.Comparison
