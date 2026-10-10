import Holant.Complexity.BinaryArithmetic.EncodedAddition
import Holant.Complexity.BinaryArithmetic.Comparison
import Holant.Complexity.MachineFrame
import Holant.Algebraic.RationalEncoding

/-!
# Serialized binary strict comparison in genuine polynomial time

This parser reuses `EncodedAddition.inputEncoding`, preserving its faithful
single-input pair representation. The finite borrow recurrence consumes every
operand bit and returns one Boolean symbol. All scratch stacks are empty at halt,
and every parser and comparison transition is included in the polynomial bound.
-/

namespace Holant.Complexity.BinaryArithmetic.EncodedComparison

open Turing Computability
open Turing.TM2.Stmt
open Comparison

abbrev inputEncoding := EncodedAddition.inputEncoding

abbrev K := Comparison.Stack ⊕ Unit
abbrev Label := Unit ⊕ Bool
abbrev Memory := Comparison.State × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

/-- The parser's only register is the existing optional-bit scratch field. -/
def saveBit (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), v.2)

def clear : Memory := (Comparison.initial, ())

/-- The first phase consumes a `true, bit` pair or the `false` delimiter.
The second phase consumes the remainder, then jumps to the compiled comparator. -/
def parser : Bool → Statement
  | false => pop (.inr ()) saveBit
      (branch (fun v => v.1.2.1.getD false)
        (pop (.inr ()) saveBit
          (push (.inl .left) (fun v => v.1.2.1.getD false)
            (load (fun _ => clear) (goto (fun _ => .inr false)))))
        (load (fun _ => clear) (goto (fun _ => .inr true))))
  | true => pop (.inr ()) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .right) (fun v => v.1.2.1.getD false)
          (load (fun _ => clear) (goto (fun _ => .inr true))))
        (load (fun _ => clear) (goto (fun _ => .inl ()))))

abbrev computer : FinTM2 where
  K := K
  k₀ := .inr ()
  k₁ := .inl .out
  Γ _ := Bool
  Λ := Label
  main := .inr false
  σ := Memory
  initialState := clear
  m := MachineFrame.program Comparison.program parser

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def parserCfg (phase : Bool) (input a b : List Bool) : Config :=
  ⟨some (.inr phase), clear, Sum.elim (Comparison.tapes a b [] []) (fun _ => input)⟩

def comparatorCfg (c : Comparison.Config) : Config := MachineFrame.cfg c () (fun _ : Unit => [])

@[simp] theorem update_input (source : Comparison.Stack → List Bool) (input word : List Bool) :
    Function.update (Sum.elim source (fun _ : Unit => input)) (.inr ()) word =
      Sum.elim source (fun _ : Unit => word) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k; simp

@[simp] theorem step_first_cons (x : Bool) (rest a b : List Bool) :
    computer.step (parserCfg false (true :: x :: rest) a b) =
      some (parserCfg false rest (x :: a) b) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Comparison.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_delimiter (rest a b : List Bool) :
    computer.step (parserCfg false (false :: rest) a b) =
      some (parserCfg true rest a b) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Comparison.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_cons (x : Bool) (rest a b : List Bool) :
    computer.step (parserCfg true (x :: rest) a b) =
      some (parserCfg true rest a (x :: b)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Comparison.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_nil (a b : List Bool) :
    computer.step (parserCfg true [] a b) =
      some (comparatorCfg (Comparison.cfg (some ()) false a b [])) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Comparison.initial, comparatorCfg, MachineFrame.cfg, Comparison.cfg,
    Comparison.reset]
  congr 2

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

/-- Exact preparation of the first operand while retaining the untouched suffix. -/
theorem first_exact (word rest a b : List Bool) :
    Runs (parserCfg false (Holant.Algebraic.frame word ++ rest) a b)
      (parserCfg true rest (word.reverse ++ a) b) (word.length + 1) := by
  induction word generalizing a with
  | nil => simpa [Holant.Algebraic.frame] using Runs.one (step_delimiter rest a b)
  | cons bit word ih =>
    have h := (Runs.one (step_first_cons bit (Holant.Algebraic.frame word ++ rest) a b)).trans
      (ih (bit :: a))
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

/-- Exact preparation of the second operand and transfer to comparison control. -/
theorem second_exact (word a b : List Bool) :
    Runs (parserCfg true word a b)
      (comparatorCfg (Comparison.cfg (some ()) false a (word.reverse ++ b) []))
      (word.length + 1) := by
  induction word generalizing b with
  | nil => simpa using Runs.one (step_second_nil a b)
  | cons bit word ih =>
    have h := (Runs.one (step_second_cons bit word a b)).trans (ih (bit :: b))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Initialization is exactly mathlib's single-input convention. -/
theorem parserCfg_init (input : List Bool) :
    parserCfg false input [] [] = initList computer input := by
  dsimp [parserCfg, initList, clear, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

/-- The final state is exactly mathlib's clean-output convention. -/
theorem comparatorCfg_halt (output : List Bool) :
    comparatorCfg (Comparison.cfg none false [] [] output) = haltList computer output := by
  dsimp [comparatorCfg, MachineFrame.cfg, Comparison.cfg, haltList, computer, clear, Comparison.reset, Comparison.initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

/-- The compiled source execution preserves every transition, including halt. -/
theorem lift_comparison {a b : Comparison.Config} {time : ℕ} (h : Comparison.Runs a b time) :
    Runs (comparatorCfg a) (comparatorCfg b) time := by
  unfold Runs comparatorCfg
  change (fun d => d.bind (TM2.step (MachineFrame.program Comparison.program parser)))^[time]
    (some (MachineFrame.cfg a () (fun _ : Unit => []))) = _
  rw [MachineFrame.run_program]
  change ((fun c => c.bind Comparison.computer.step)^[time] (some a)).map _ = _
  rw [h]
  rfl

/-- All serialized-input transitions are counted against the real TM2 semantics. -/
theorem encoded_exact (a b : ℕ) :
    Runs (initList computer (inputEncoding.encode (a, b)))
      (haltList computer [decide (a < b)])
      ((encodeNat a).length + (encodeNat b).length +
        max (encodeNat a).length (encodeNat b).length + 3) := by
  have h₁ := first_exact (encodeNat a).reverse (encodeNat b).reverse [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact (encodeNat b).reverse (encodeNat a) []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := lift_comparison (Comparison.compute_encodeNat_exact a b)
  have h := (h₁.trans h₂).trans h₃
  rw [comparatorCfg_halt] at h
  rw [parserCfg_init] at h
  change Runs (initList computer (inputEncoding.encode (a, b))) _ _ at h
  convert h using 1
  simp
  omega

/-- A polynomial-time comparison witness using faithful, explicitly bounded binary codecs. -/
noncomputable def comparisonPolyTime : PolyTime inputEncoding Comparison.boolEncoding (fun p => decide (p.1 < p.2)) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 5
  outputsFun p := by
    change TM2OutputsInTime computer (List.map id (inputEncoding.encode p))
      (some (List.map id [decide (p.1 < p.2)]))
      ((3 * Polynomial.X + 5).eval (inputEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := ((encodeNat p.1).length + (encodeNat p.2).length +
               max (encodeNat p.1).length (encodeNat p.2).length + 3)
             evals_in_steps := encoded_exact p.1 p.2
             steps_le_m := ?_ }
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, EncodedAddition.inputEncoding_length]
    omega
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem comparison_inFP : InFP inputEncoding Comparison.boolEncoding (fun p => decide (p.1 < p.2)) :=
  ⟨comparisonPolyTime⟩

/-- Serialization instructions also have a fixed elementary cost. -/
theorem parser_budget (label : Bool) : TM2Cost.budget (parser label) ≤ 6 := by
  cases label <;> decide

/-- Every source and parser transition has the same uniform primitive bound. -/
theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 7 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineFrame.program, MachineFrame.budget_stmt] using
      le_of_eq (Comparison.program_budget label) |>.trans (by decide)
  | inr label => exact le_trans (parser_budget label) (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 5 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 3 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.EncodedComparison
