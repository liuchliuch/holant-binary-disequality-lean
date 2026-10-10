import Holant.Complexity.BinaryArithmetic.MultiplyBits
import Holant.Complexity.BinaryArithmetic.Addition
import Holant.Complexity.MachineReturn

/-!
# Actual finite shift/add multiplication

The six binary stacks hold the accumulator, the adder's second operand and two
work stacks, the preserved multiplicand, and remaining MSB-first multiplier bits.
Every operation is a finite TM2 statement. True multiplier bits invoke the actual
carry-adder through the structural returning compiler; explicit copying and
transfer loops preserve the multiplicand and clean the adder's work stacks.

This module proves exact prepared-stack executions and polynomial transition
bounds. The single-stream wrapper is supplied in `EncodedMultiplication`.
-/

namespace Holant.Complexity.BinaryArithmetic.Multiplication

open Turing Computability
open Turing.TM2.Stmt

inductive Phase
  | loop | copyMove | copyRestore | moveOut | restoreOut | clear
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{.loop, .copyMove, .copyRestore, .moveOut, .restoreOut, .clear}, by intro p; cases p <;> simp⟩

abbrev K := Addition.Stack ⊕ Bool
abbrev Label := Bool ⊕ Phase
abbrev Memory := Addition.State × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

def clean : Memory := (Addition.initial, ())
def saveBit (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), v.2)
def ret (_ : Unit) : Phase := .moveOut

/-- Implement canonical doubling by peeking, then conditionally pushing one zero. -/
def shiftGoto (next : Phase) : Statement :=
  peek (.inl .left) saveBit
    (branch (fun v => v.1.2.1.isSome)
      (push (.inl .left) (fun _ => false)
        (load (fun _ => clean) (goto (fun _ => .inr next))))
      (load (fun _ => clean) (goto (fun _ => .inr next))))

/-- Ordinary finite stack code surrounding the compiled carry-adder. -/
def outside : Phase → Statement
  | .loop => pop (.inr true) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (branch (fun v => v.1.2.1.getD false) (shiftGoto .copyMove) (shiftGoto .loop))
        (load (fun _ => clean) (goto (fun _ => .inr .clear))))
  | .copyMove => pop (.inr false) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .work) (fun v => v.1.2.1.getD false)
          (load (fun _ => clean) (goto (fun _ => .inr .copyMove))))
        (load (fun _ => clean) (goto (fun _ => .inr .copyRestore))))
  | .copyRestore => pop (.inl .work) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inr false) (fun v => v.1.2.1.getD false)
          (push (.inl .right) (fun v => v.1.2.1.getD false)
            (load (fun _ => clean) (goto (fun _ => .inr .copyRestore)))))
        (load (fun _ => clean) (goto (fun _ => .inl false))))
  | .moveOut => pop (.inl .out) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .work) (fun v => v.1.2.1.getD false)
          (load (fun _ => clean) (goto (fun _ => .inr .moveOut))))
        (load (fun _ => clean) (goto (fun _ => .inr .restoreOut))))
  | .restoreOut => pop (.inl .work) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .left) (fun v => v.1.2.1.getD false)
          (load (fun _ => clean) (goto (fun _ => .inr .restoreOut))))
        (load (fun _ => clean) (goto (fun _ => .inr .loop))))
  | .clear => pop (.inr false) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (load (fun _ => clean) (goto (fun _ => .inr .clear)))
        (load (fun _ => clean) halt))

abbrev computer : FinTM2 where
  K := K
  k₀ := .inr false
  k₁ := .inl .left
  Γ _ := Bool
  Λ := Label
  main := .inr .loop
  σ := Memory
  initialState := clean
  m := MachineReturn.program ret Addition.program outside

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def extras (m digits : List Bool) : Bool → List Bool
  | false => m
  | true => digits

def tapes (a r w o m digits : List Bool) : K → List Bool :=
  Sum.elim (Addition.tapes a r w o) (extras m digits)

def cfg (label : Option Label) (a r w o m digits : List Bool) : Config :=
  ⟨label, clean, tapes a r w o m digits⟩

@[simp] theorem tapes_left (a r w o m ds : List Bool) : tapes a r w o m ds (.inl .left) = a := rfl
@[simp] theorem tapes_right (a r w o m ds : List Bool) : tapes a r w o m ds (.inl .right) = r := rfl
@[simp] theorem tapes_work (a r w o m ds : List Bool) : tapes a r w o m ds (.inl .work) = w := rfl
@[simp] theorem tapes_out (a r w o m ds : List Bool) : tapes a r w o m ds (.inl .out) = o := rfl
@[simp] theorem tapes_m (a r w o m ds : List Bool) : tapes a r w o m ds (.inr false) = m := rfl
@[simp] theorem tapes_digits (a r w o m ds : List Bool) : tapes a r w o m ds (.inr true) = ds := rfl

@[simp] theorem update_left (a r w o m ds x : List Bool) :
    Function.update (tapes a r w o m ds) (.inl .left) x = tapes x r w o m ds := by
  funext k; cases k with
  | inl k => cases k <;> simp [tapes]
  | inr k => cases k <;> simp [tapes]
@[simp] theorem update_right (a r w o m ds x : List Bool) :
    Function.update (tapes a r w o m ds) (.inl .right) x = tapes a x w o m ds := by
  funext k; cases k with
  | inl k => cases k <;> simp [tapes]
  | inr k => cases k <;> simp [tapes]
@[simp] theorem update_work (a r w o m ds x : List Bool) :
    Function.update (tapes a r w o m ds) (.inl .work) x = tapes a r x o m ds := by
  funext k; cases k with
  | inl k => cases k <;> simp [tapes]
  | inr k => cases k <;> simp [tapes]
@[simp] theorem update_out (a r w o m ds x : List Bool) :
    Function.update (tapes a r w o m ds) (.inl .out) x = tapes a r w x m ds := by
  funext k; cases k with
  | inl k => cases k <;> simp [tapes]
  | inr k => cases k <;> simp [tapes]
@[simp] theorem update_m (a r w o m ds x : List Bool) :
    Function.update (tapes a r w o m ds) (.inr false) x = tapes a r w o x ds := by
  funext k; cases k with
  | inl k => cases k <;> simp [tapes]
  | inr k => cases k <;> simp [tapes, extras]
@[simp] theorem update_digits (a r w o m ds x : List Bool) :
    Function.update (tapes a r w o m ds) (.inr true) x = tapes a r w o m x := by
  funext k; cases k with
  | inl k => cases k <;> simp [tapes]
  | inr k => cases k <;> simp [tapes, extras]

def Runs (start finish : Config) (time : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[time] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

/-- The multiplier is consumed one bit per outer-loop transition. -/
theorem step_loop (bit : Bool) (a m digits : List Bool) :
    computer.step (cfg (some (.inr .loop)) a [] [] [] m (bit :: digits)) =
      some (cfg (some (.inr (if bit then .copyMove else .loop)))
        (Doubling.shift a) [] [] [] m digits) := by
  cases bit <;> cases a <;>
    simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, shiftGoto,
      cfg, TM2.stepAux, clean, saveBit, Addition.initial, Doubling.shift] <;> congr 2

theorem step_loop_nil (a m : List Bool) :
    computer.step (cfg (some (.inr .loop)) a [] [] [] m []) =
      some (cfg (some (.inr .clear)) a [] [] [] m []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_copyMove_cons (bit : Bool) (a m w digits : List Bool) :
    computer.step (cfg (some (.inr .copyMove)) a [] w [] (bit :: m) digits) =
      some (cfg (some (.inr .copyMove)) a [] (bit :: w) [] m digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_copyMove_nil (a w digits : List Bool) :
    computer.step (cfg (some (.inr .copyMove)) a [] w [] [] digits) =
      some (cfg (some (.inr .copyRestore)) a [] w [] [] digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_copyRestore_cons (bit : Bool) (a r w m digits : List Bool) :
    computer.step (cfg (some (.inr .copyRestore)) a r (bit :: w) [] m digits) =
      some (cfg (some (.inr .copyRestore)) a (bit :: r) w [] (bit :: m) digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_copyRestore_nil (a r m digits : List Bool) :
    computer.step (cfg (some (.inr .copyRestore)) a r [] [] m digits) =
      some (cfg (some (.inl false)) a r [] [] m digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem copyMove_exact (a m w digits : List Bool) :
    Runs (cfg (some (.inr .copyMove)) a [] w [] m digits)
      (cfg (some (.inr .copyRestore)) a [] (m.reverse ++ w) [] [] digits) (m.length + 1) := by
  induction m generalizing w with
  | nil => simpa using Runs.one (step_copyMove_nil a w digits)
  | cons bit m ih =>
    have h := (Runs.one (step_copyMove_cons bit a m w digits)).trans (ih (bit :: w))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem copyRestore_exact (a w r m digits : List Bool) :
    Runs (cfg (some (.inr .copyRestore)) a r w [] m digits)
      (cfg (some (.inl false)) a (w.reverse ++ r) [] [] (w.reverse ++ m) digits) (w.length + 1) := by
  induction w generalizing r m with
  | nil => simpa using Runs.one (step_copyRestore_nil a r m digits)
  | cons bit w ih =>
    have h := (Runs.one (step_copyRestore_cons bit a r w m digits)).trans (ih (bit :: r) (bit :: m))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Explicit move/restore loops copy the preserved multiplicand into the adder. -/
theorem copy_exact (a m digits : List Bool) :
    Runs (cfg (some (.inr .copyMove)) a [] [] [] m digits)
      (cfg (some (.inl false)) a m [] [] m digits) (2 * (m.length + 1)) := by
  have hm := copyMove_exact a m [] digits
  simp only [List.append_nil] at hm
  have h := hm.trans (copyRestore_exact a m.reverse [] [] digits)
  simpa [Nat.two_mul] using h

/-- The existing carry-adder runs with identical real transitions and returns
at the explicit transfer label, preserving both outer stacks. -/
theorem addition_exact (a b m digits : List Bool) :
    Runs (cfg (some (.inl false)) a b [] [] m digits)
      (cfg (some (.inr .moveOut)) [] [] [] (addBits false a b) m digits)
      (max a.length b.length + (addBits false a b).length + 2) := by
  have h := MachineReturn.run_program ret Addition.program outside
    (Addition.cfg (some false) false a b [] []) () (extras m digits)
    (max a.length b.length + (addBits false a b).length + 2)
    (Addition.cfg none false [] [] [] (addBits false a b)) (Addition.compute_exact false a b)
  simpa only [Runs, FinTM2.step, computer, MachineReturn.cfg, Addition.cfg, Addition.reset,
    cfg, clean, Addition.initial, tapes, ret, Option.elim_some, Option.elim_none] using h

theorem step_moveOut_cons (bit : Bool) (w o m digits : List Bool) :
    computer.step (cfg (some (.inr .moveOut)) [] [] w (bit :: o) m digits) =
      some (cfg (some (.inr .moveOut)) [] [] (bit :: w) o m digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_moveOut_nil (w m digits : List Bool) :
    computer.step (cfg (some (.inr .moveOut)) [] [] w [] m digits) =
      some (cfg (some (.inr .restoreOut)) [] [] w [] m digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_restoreOut_cons (bit : Bool) (a w m digits : List Bool) :
    computer.step (cfg (some (.inr .restoreOut)) a [] (bit :: w) [] m digits) =
      some (cfg (some (.inr .restoreOut)) (bit :: a) [] w [] m digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_restoreOut_nil (a m digits : List Bool) :
    computer.step (cfg (some (.inr .restoreOut)) a [] [] [] m digits) =
      some (cfg (some (.inr .loop)) a [] [] [] m digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem moveOut_exact (o w m digits : List Bool) :
    Runs (cfg (some (.inr .moveOut)) [] [] w o m digits)
      (cfg (some (.inr .restoreOut)) [] [] (o.reverse ++ w) [] m digits) (o.length + 1) := by
  induction o generalizing w with
  | nil => simpa using Runs.one (step_moveOut_nil w m digits)
  | cons bit o ih =>
    have h := (Runs.one (step_moveOut_cons bit w o m digits)).trans (ih (bit :: w))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem restoreOut_exact (w a m digits : List Bool) :
    Runs (cfg (some (.inr .restoreOut)) a [] w [] m digits)
      (cfg (some (.inr .loop)) (w.reverse ++ a) [] [] [] m digits) (w.length + 1) := by
  induction w generalizing a with
  | nil => simpa using Runs.one (step_restoreOut_nil a m digits)
  | cons bit w ih =>
    have h := (Runs.one (step_restoreOut_cons bit a w m digits)).trans (ih (bit :: a))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Two real transfer loops replace the consumed accumulator by the adder result. -/
theorem transfer_exact (o m digits : List Bool) :
    Runs (cfg (some (.inr .moveOut)) [] [] [] o m digits)
      (cfg (some (.inr .loop)) o [] [] [] m digits) (2 * (o.length + 1)) := by
  have hm := moveOut_exact o [] m digits
  simp only [List.append_nil] at hm
  have h := hm.trans (restoreOut_exact o.reverse [] m digits)
  simpa [Nat.two_mul] using h

theorem step_clear_cons (bit : Bool) (a m : List Bool) :
    computer.step (cfg (some (.inr .clear)) a [] [] [] (bit :: m) []) =
      some (cfg (some (.inr .clear)) a [] [] [] m []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem step_clear_nil (a : List Bool) :
    computer.step (cfg (some (.inr .clear)) a [] [] [] [] []) =
      some (cfg none a [] [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    cfg, TM2.stepAux, clean, saveBit, Addition.initial]
  congr 2

theorem clear_exact (a m : List Bool) :
    Runs (cfg (some (.inr .clear)) a [] [] [] m [])
      (cfg none a [] [] [] [] []) (m.length + 1) := by
  induction m with
  | nil => exact Runs.one (step_clear_nil a)
  | cons bit m ih => exact (Runs.one (step_clear_cons bit a m)).trans ih

/-- The complete shift/add column, including multiplicand preservation and all
transfers, has exactly the word-level specification's transition count. -/
theorem column_exact (bit : Bool) (a m digits : List Bool) :
    Runs (cfg (some (.inr .loop)) a [] [] [] m (bit :: digits))
      (cfg (some (.inr .loop)) (MultiplyBits.next bit m a) [] [] [] m digits)
      (MultiplyBits.columnTime bit m a) := by
  cases bit with
  | false => simpa [MultiplyBits.next, MultiplyBits.columnTime] using Runs.one (step_loop false a m digits)
  | true =>
    have hs := Runs.one (step_loop true a m digits)
    simp only [↓reduceIte] at hs
    have hc := copy_exact (Doubling.shift a) m digits
    have ha := addition_exact (Doubling.shift a) m m digits
    have ht := transfer_exact (addBits false (Doubling.shift a) m) m digits
    have h := ((hs.trans hc).trans ha).trans ht
    simp only [MultiplyBits.columnTime, MultiplyBits.next, ↓reduceIte]
    convert h using 1
    omega

/-- Exact complete multiplication, ending with only the result stack nonempty. -/
theorem run_exact (m digits a : List Bool) :
    Runs (cfg (some (.inr .loop)) a [] [] [] m digits)
      (cfg none (MultiplyBits.run m digits a) [] [] [] [] []) (MultiplyBits.time m digits a) := by
  induction digits generalizing a with
  | nil =>
    have h := (Runs.one (step_loop_nil a m)).trans (clear_exact a m)
    simpa [MultiplyBits.run, MultiplyBits.time, Nat.add_assoc] using h
  | cons bit rest ih =>
    have h := (column_exact bit a m rest).trans (ih (MultiplyBits.next bit m a))
    simpa [MultiplyBits.run, MultiplyBits.time, Nat.add_comm] using h

/-- Exact canonical encoded product, rather than correctness only up to decoding. -/
theorem compute_encodeNat_exact (a b : ℕ) :
    Runs (cfg (some (.inr .loop)) [] [] [] [] (encodeNat a) (encodeNat b).reverse)
      (cfg none (encodeNat (a * b)) [] [] [] [] [])
      (MultiplyBits.time (encodeNat a) (encodeNat b).reverse []) := by
  simpa only [MultiplyBits.run_encodeNat] using run_exact (encodeNat a) (encodeNat b).reverse []

/-- A polynomial bound on actual prepared-stack multiplication transitions. -/
def compute_timed (m digits a : List Bool) :
    StateTransition.EvalsToInTime computer.step (cfg (some (.inr .loop)) a [] [] [] m digits)
      (some (cfg none (MultiplyBits.run m digits a) [] [] [] [] []))
      ((digits.length + 1) * (6 * (a.length + (digits.length + 1) * (m.length + 2) + 3))) where
  steps := MultiplyBits.time m digits a
  evals_in_steps := run_exact m digits a
  steps_le_m := MultiplyBits.time_le m digits a

theorem outside_budget (phase : Phase) : TM2Cost.budget (outside phase) ≤ 8 := by
  cases phase <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 8 := by
  cases label with
  | inl label =>
    apply le_trans _ (by decide : 7 ≤ 8)
    simpa only [computer, MachineReturn.program, MachineReturn.budget_stmt] using Addition.program_budget label
  | inr phase => exact outside_budget phase

@[simp] theorem stack_count : Fintype.card computer.K = 6 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 8 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.Multiplication
