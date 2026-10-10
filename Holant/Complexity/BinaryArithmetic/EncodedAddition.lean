import Holant.Complexity.BinaryArithmetic.Addition
import Holant.Complexity.MachineFrame
import Holant.Algebraic.RationalEncoding

/-!
# Serialized binary addition in genuine polynomial time

A faithful binary encoding stores a framed, most-significant-bit-first first
operand followed by the most-significant-bit-first second operand. Its length is
`2 * firstBitLength + secondBitLength + 1`; no magnitude is hidden in a symbol.
An actual two-label parser pushes each bit onto the operand stacks, then the
proved carry-adder runs via the structural machine-frame compiler. The resulting
`PolyTime` witness uses one binary input stream and the canonical `encodeNat`
output stream, and has only five binary stacks and eighteen register states.

Conversion from other paired codecs, multiplication, integer signs, rational
normalization and number-field arithmetic are not claimed here.
-/

namespace Holant.Complexity.BinaryArithmetic.EncodedAddition

open Turing Computability
open Turing.TM2.Stmt
open Addition

/-- Framing distinguishes the first operand, including the empty zero word. -/
def inputEncoding : Encoding (ℕ × ℕ) Bool where
  encode p := Holant.Algebraic.frame (encodeNat p.1).reverse ++ (encodeNat p.2).reverse
  decode bits := (Holant.Algebraic.unframe bits).map
    (fun p => (decodeNat p.1.reverse, decodeNat p.2.reverse))
  decode_encode p := by simp

@[simp] theorem inputEncoding_length (p : ℕ × ℕ) :
    (inputEncoding.encode p).length = 2 * (encodeNat p.1).length + (encodeNat p.2).length + 1 := by
  simp [inputEncoding, Holant.Algebraic.frame_length]
  omega

abbrev K := Addition.Stack ⊕ Unit
abbrev Label := Bool ⊕ Bool
abbrev Memory := Addition.State × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

/-- The parser's only register is the existing optional-bit scratch field. -/
def saveBit (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), v.2)

def clear : Memory := (Addition.initial, ())

/-- The first phase consumes a `true, bit` pair or the `false` delimiter.
The second phase consumes the remainder, then jumps to the compiled adder. -/
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
        (load (fun _ => clear) (goto (fun _ => .inl false))))

abbrev computer : FinTM2 where
  K := K
  k₀ := .inr ()
  k₁ := .inl .out
  Γ _ := Bool
  Λ := Label
  main := .inr false
  σ := Memory
  initialState := clear
  m := MachineFrame.program Addition.program parser

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def parserCfg (phase : Bool) (input a b : List Bool) : Config :=
  ⟨some (.inr phase), clear, Sum.elim (Addition.tapes a b [] []) (fun _ => input)⟩

def adderCfg (c : Addition.Config) : Config := MachineFrame.cfg c () (fun _ : Unit => [])

@[simp] theorem update_input (source : Addition.Stack → List Bool) (input word : List Bool) :
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
    TM2.stepAux, saveBit, clear, Addition.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_delimiter (rest a b : List Bool) :
    computer.step (parserCfg false (false :: rest) a b) =
      some (parserCfg true rest a b) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Addition.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_cons (x : Bool) (rest a b : List Bool) :
    computer.step (parserCfg true (x :: rest) a b) =
      some (parserCfg true rest a (x :: b)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Addition.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_nil (a b : List Bool) :
    computer.step (parserCfg true [] a b) =
      some (adderCfg (Addition.cfg (some false) false a b [] [])) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Addition.initial, adderCfg, MachineFrame.cfg, Addition.cfg,
    Addition.reset]
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

/-- Exact preparation of the second operand and transfer to addition control. -/
theorem second_exact (word a b : List Bool) :
    Runs (parserCfg true word a b)
      (adderCfg (Addition.cfg (some false) false a (word.reverse ++ b) [] []))
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
theorem adderCfg_halt (output : List Bool) :
    adderCfg (Addition.cfg none false [] [] [] output) = haltList computer output := by
  dsimp [adderCfg, MachineFrame.cfg, Addition.cfg, haltList, computer, clear, Addition.reset, Addition.initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

/-- The compiled source execution preserves every transition, including halt. -/
theorem lift_addition {a b : Addition.Config} {time : ℕ} (h : Addition.Runs a b time) :
    Runs (adderCfg a) (adderCfg b) time := by
  unfold Runs adderCfg
  change (fun d => d.bind (TM2.step (MachineFrame.program Addition.program parser)))^[time]
    (some (MachineFrame.cfg a () (fun _ : Unit => []))) = _
  rw [MachineFrame.run_program]
  change ((fun c => c.bind Addition.computer.step)^[time] (some a)).map _ = _
  rw [h]
  rfl

/-- All serialized-input transitions are counted against the real TM2 semantics. -/
theorem encoded_exact (a b : ℕ) :
    Runs (initList computer (inputEncoding.encode (a, b)))
      (haltList computer (encodeNat (a + b)))
      ((encodeNat a).length + (encodeNat b).length +
        max (encodeNat a).length (encodeNat b).length + (encodeNat (a + b)).length + 4) := by
  have h₁ := first_exact (encodeNat a).reverse (encodeNat b).reverse [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact (encodeNat b).reverse (encodeNat a) []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := lift_addition (Addition.compute_encodeNat_exact a b)
  have h := (h₁.trans h₂).trans h₃
  rw [adderCfg_halt] at h
  rw [parserCfg_init] at h
  change Runs (initList computer (inputEncoding.encode (a, b))) _ _ at h
  convert h using 1
  simp
  omega

/-- A polynomial-time addition witness using faithful, explicitly bounded binary codecs. -/
noncomputable def additionPolyTime : PolyTime inputEncoding encodingNatBool (fun p => p.1 + p.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X + 5
  outputsFun p := by
    change TM2OutputsInTime computer (List.map id (inputEncoding.encode p))
      (some (List.map id (encodeNat (p.1 + p.2))))
      ((3 * Polynomial.X + 5).eval (inputEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := ((encodeNat p.1).length + (encodeNat p.2).length +
               max (encodeNat p.1).length (encodeNat p.2).length + (encodeNat (p.1 + p.2)).length + 4)
             evals_in_steps := encoded_exact p.1 p.2
             steps_le_m := ?_ }
    have hb := addBits_length_le false (encodeNat p.1) (encodeNat p.2)
    rw [addBits_encodeNat] at hb
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, inputEncoding_length]
    omega
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem addition_inFP : InFP inputEncoding encodingNatBool (fun p => p.1 + p.2) :=
  ⟨additionPolyTime⟩

/-- Serialization instructions also have a fixed elementary cost. -/
theorem parser_budget (label : Bool) : TM2Cost.budget (parser label) ≤ 6 := by
  cases label <;> decide

/-- Every source and parser transition has the same uniform primitive bound. -/
theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 7 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineFrame.program, MachineFrame.budget_stmt] using
      Addition.program_budget label
  | inr label => exact le_trans (parser_budget label) (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 5 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 4 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.EncodedAddition
