import Holant.Complexity.BinaryArithmetic.Bits
import Holant.Complexity.StepCost

/-!
# A finite binary carry-adder with exact operational time

Four binary stacks and eighteen finite register states implement addition. Each
addition transition pops at most one bit from each operand and emits one sum bit.
A second loop reverses the accumulator into canonical least-significant-bit order.
The input contract in this module is two prepared operand stacks; serialization
into the single designated input stack is a separate interface obligation.
-/

namespace Holant.Complexity.BinaryArithmetic.Addition

open Turing
open Turing.TM2.Stmt
open Computability

inductive Stack
  | left | right | work | out
  deriving DecidableEq

instance : Fintype Stack := ⟨{.left, .right, .work, .out}, by intro k; cases k <;> simp⟩

/-- Carry and two optional bits; no unbounded arithmetic enters the register. -/
abbrev State := Bool × Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Bool State
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Bool State

def initial : State := (false, none, none)

def reset (carry : Bool) : State := (carry, none, none)

/-- `false` adds columns; `true` reverses the completed result. -/
def program : Bool → Statement
  | false =>
    pop .left (fun v x => (v.1, x, v.2.2))
      (pop .right (fun v y => (v.1, v.2.1, y))
        (branch (fun v => v.2.1.isSome || v.2.2.isSome)
          (push .work (fun v => digitSum v.1 (v.2.1.getD false) (v.2.2.getD false))
            (load (fun v => reset (digitCarry v.1 (v.2.1.getD false) (v.2.2.getD false)))
              (goto (fun _ => false))))
          (branch (fun v => v.1)
            (push .work (fun _ => true) (load (fun _ => initial) (goto (fun _ => true))))
            (load (fun _ => initial) (goto (fun _ => true))))))
  | true =>
    pop .work (fun v x => (v.1, x, v.2.2))
      (branch (fun v => v.2.1.isSome)
        (push .out (fun v => v.2.1.getD false)
          (load (fun _ => initial) (goto (fun _ => true))))
        (load (fun _ => initial) halt))

/-- A real bundled finite TM2; prepared-input correctness is stated below. -/
abbrev computer : FinTM2 where
  K := Stack
  k₀ := .left
  k₁ := .out
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := State
  initialState := initial
  m := program

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

/-- Explicit stack content specification, without encoding arithmetic as an instruction. -/
def tapes (a b w o : List Bool) : Stack → List Bool
  | .left => a
  | .right => b
  | .work => w
  | .out => o

@[simp] theorem tapes_left (a b w o : List Bool) : tapes a b w o .left = a := rfl
@[simp] theorem tapes_right (a b w o : List Bool) : tapes a b w o .right = b := rfl
@[simp] theorem tapes_work (a b w o : List Bool) : tapes a b w o .work = w := rfl
@[simp] theorem tapes_out (a b w o : List Bool) : tapes a b w o .out = o := rfl

@[simp] theorem update_left (a b w o x : List Bool) :
    Function.update (tapes a b w o) .left x = tapes x b w o := by
  funext k; cases k <;> simp [tapes]
@[simp] theorem update_right (a b w o x : List Bool) :
    Function.update (tapes a b w o) .right x = tapes a x w o := by
  funext k; cases k <;> simp [tapes]
@[simp] theorem update_work (a b w o x : List Bool) :
    Function.update (tapes a b w o) .work x = tapes a b x o := by
  funext k; cases k <;> simp [tapes]
@[simp] theorem update_out (a b w o x : List Bool) :
    Function.update (tapes a b w o) .out x = tapes a b w x := by
  funext k; cases k <;> simp [tapes]

def cfg (label : Option Bool) (carry : Bool) (a b w o : List Bool) : Config :=
  ⟨label, reset carry, tapes a b w o⟩

/-- Actual iterated machine transition relation, retaining the final configuration. -/
def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

/-- A run gives a mathlib timed transition witness with the same exact count. -/
def Runs.toTimed {a b : Config} {n : ℕ} (h : Runs a b n) :
    StateTransition.EvalsToInTime computer.step a (some b) n where
  steps := n
  evals_in_steps := h
  steps_le_m := Nat.le_refl n

@[simp] theorem step_add_both (carry x y : Bool) (a b w o : List Bool) :
    computer.step (cfg (some false) carry (x :: a) (y :: b) w o) =
      some (cfg (some false) (digitCarry carry x y) a b (digitSum carry x y :: w) o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes]
  congr 2

@[simp] theorem step_add_left (carry x : Bool) (a w o : List Bool) :
    computer.step (cfg (some false) carry (x :: a) [] w o) =
      some (cfg (some false) (digitCarry carry x false) a [] (digitSum carry x false :: w) o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes]
  congr 2

@[simp] theorem step_add_right (carry y : Bool) (b w o : List Bool) :
    computer.step (cfg (some false) carry [] (y :: b) w o) =
      some (cfg (some false) (digitCarry carry false y) [] b (digitSum carry false y :: w) o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, tapes]
  congr 2

@[simp] theorem step_add_done (carry : Bool) (w o : List Bool) :
    computer.step (cfg (some false) carry [] [] w o) =
      some (cfg (some true) false [] [] ((if carry then [true] else []) ++ w) o) := by
  cases carry <;>
    simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes] <;>
    congr 2

/-- Each input column takes one transition, followed by one carry/phase transition. -/
theorem add_exact (carry : Bool) (a b w o : List Bool) :
    Runs (cfg (some false) carry a b w o)
      (cfg (some true) false [] [] ((addBits carry a b).reverse ++ w) o)
      (max a.length b.length + 1) := by
  induction a generalizing b carry w with
  | nil =>
    induction b generalizing carry w with
    | nil =>
      cases carry
      · simpa [addBits] using Runs.one (step_add_done false w o)
      · simpa [addBits] using Runs.one (step_add_done true w o)
    | cons y b ih =>
      have h := (Runs.one (step_add_right carry y b w o)).trans
        (ih (digitCarry carry false y) (digitSum carry false y :: w))
      simpa [addBits, List.reverse_cons, List.append_assoc] using h
  | cons x a ih =>
    cases b with
    | nil =>
      have h := (Runs.one (step_add_left carry x a w o)).trans
        (ih (digitCarry carry x false) [] (digitSum carry x false :: w))
      simpa [addBits, List.reverse_cons, List.append_assoc] using h
    | cons y b =>
      have h := (Runs.one (step_add_both carry x y a b w o)).trans
        (ih (digitCarry carry x y) b (digitSum carry x y :: w))
      simpa [addBits, List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h

@[simp] theorem step_reverse_cons (x : Bool) (w o : List Bool) :
    computer.step (cfg (some true) false [] [] (x :: w) o) =
      some (cfg (some true) false [] [] w (x :: o)) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes]
  congr 2

@[simp] theorem step_reverse_nil (o : List Bool) :
    computer.step (cfg (some true) false [] [] [] o) =
      some (cfg none false [] [] [] o) := by
  simp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux, reset, initial, tapes]
  congr 2

/-- The output reversal also has an exact linear transition count. -/
theorem reverse_exact (w o : List Bool) :
    Runs (cfg (some true) false [] [] w o)
      (cfg none false [] [] [] (w.reverse ++ o)) (w.length + 1) := by
  induction w generalizing o with
  | nil => simpa using Runs.one (step_reverse_nil o)
  | cons x w ih =>
    have h := (Runs.one (step_reverse_cons x w o)).trans (ih (x :: o))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Full addition preserves exact bit strings and cleans every scratch stack. -/
theorem compute_exact (carry : Bool) (a b : List Bool) :
    Runs (cfg (some false) carry a b [] [])
      (cfg none false [] [] [] (addBits carry a b))
      (max a.length b.length + (addBits carry a b).length + 2) := by
  have ha := add_exact carry a b [] []
  simp only [List.append_nil] at ha
  have h := ha.trans (reverse_exact (addBits carry a b).reverse [])
  convert h using 1 <;> simp
  omega

/-- Genuine bit-time upper bound for prepared arbitrary binary operands. -/
def compute_timed (carry : Bool) (a b : List Bool) :
    StateTransition.EvalsToInTime computer.step (cfg (some false) carry a b [] [])
      (some (cfg none false [] [] [] (addBits carry a b)))
      (2 * max a.length b.length + 3) where
  steps := max a.length b.length + (addBits carry a b).length + 2
  evals_in_steps := compute_exact carry a b
  steps_le_m := by have := addBits_length_le carry a b; omega

/-- Canonical arithmetic correctness uses the actual project natural-number codec. -/
theorem compute_encodeNat_exact (a b : ℕ) :
    Runs (cfg (some false) false (encodeNat a) (encodeNat b) [] [])
      (cfg none false [] [] [] (encodeNat (a + b)))
      (max (encodeNat a).length (encodeNat b).length + (encodeNat (a + b)).length + 2) := by
  simpa only [addBits_encodeNat] using compute_exact false (encodeNat a) (encodeNat b)

/-- The finite straight-line syntax has a constant elementary-instruction budget. -/
theorem program_budget (label : Bool) : TM2Cost.budget (program label) ≤ 7 := by
  cases label <;> decide

end Holant.Complexity.BinaryArithmetic.Addition
