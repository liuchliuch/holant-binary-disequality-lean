import Holant.Complexity.BinaryArithmetic.Multiplication
import Holant.Complexity.BinaryArithmetic.EncodedAddition

/-!
# Faithfully encoded multiplication in genuine finite-machine polynomial time

The input codec is exactly the previously verified addition codec. Three finite
parser phases load the multiplicand, load and reverse the multiplier, and enter
the actual shift/add machine. Every preparatory, arithmetic, transfer, cleanup
and halting transition is counted. The output is literally `encodeNat (a * b)`.

Seven binary stacks, eleven control labels and eighteen finite states suffice.
The bound is deliberately loose and cubic. No host-level arithmetic or unbounded
word transformation occurs inside the machine's instruction functions.
-/

namespace Holant.Complexity.BinaryArithmetic.EncodedMultiplication

open Turing Computability
open Turing.TM2.Stmt

abbrev inputEncoding := EncodedAddition.inputEncoding

inductive Phase
  | first | second | reverse
  deriving DecidableEq

instance : Fintype Phase := ⟨{.first, .second, .reverse}, by intro p; cases p <;> simp⟩

abbrev K := Multiplication.K ⊕ Unit
abbrev Label := Multiplication.Label ⊕ Phase
abbrev Memory := Multiplication.Memory × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

def clean : Memory := (Multiplication.clean, ())
def saveBit (v : Memory) (bit : Option Bool) : Memory := (Multiplication.saveBit v.1 bit, v.2)

def parser : Phase → Statement
  | .first => pop (.inr ()) saveBit
      (branch (fun v => v.1.1.2.1.getD false)
        (pop (.inr ()) saveBit
          (push (.inl (.inr false)) (fun v => v.1.1.2.1.getD false)
            (load (fun _ => clean) (goto (fun _ => .inr .first)))))
        (load (fun _ => clean) (goto (fun _ => .inr .second))))
  | .second => pop (.inr ()) saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push (.inl (.inl .right)) (fun v => v.1.1.2.1.getD false)
          (load (fun _ => clean) (goto (fun _ => .inr .second))))
        (load (fun _ => clean) (goto (fun _ => .inr .reverse))))
  | .reverse => pop (.inl (.inl .right)) saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push (.inl (.inr true)) (fun v => v.1.1.2.1.getD false)
          (load (fun _ => clean) (goto (fun _ => .inr .reverse))))
        (load (fun _ => clean) (goto (fun _ => .inl (.inr .loop)))))

abbrev computer : FinTM2 where
  K := K
  k₀ := .inr ()
  k₁ := .inl (.inl .left)
  Γ _ := Bool
  Λ := Label
  main := .inr .first
  σ := Memory
  initialState := clean
  m := MachineFrame.program Multiplication.computer.m parser

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def parserCfg (phase : Phase) (input m tmp digits : List Bool) : Config :=
  ⟨some (.inr phase), clean,
    Sum.elim (Multiplication.tapes [] tmp [] [] m digits) (fun _ => input)⟩

def sourceCfg (c : Multiplication.Config) : Config :=
  MachineFrame.cfg c () (fun _ : Unit => [])

@[simp] theorem update_input (source : Multiplication.K → List Bool) (input word : List Bool) :
    Function.update (Sum.elim source (fun _ : Unit => input)) (.inr ()) word =
      Sum.elim source (fun _ : Unit => word) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k; simp

theorem step_first_cons (bit : Bool) (input m tmp digits : List Bool) :
    computer.step (parserCfg .first (true :: bit :: input) m tmp digits) =
      some (parserCfg .first input (bit :: m) tmp digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clean, Multiplication.saveBit, Multiplication.clean, Addition.initial,
    MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem step_delimiter (input m tmp digits : List Bool) :
    computer.step (parserCfg .first (false :: input) m tmp digits) =
      some (parserCfg .second input m tmp digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clean, Multiplication.saveBit, Multiplication.clean, Addition.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem step_second_cons (bit : Bool) (input m tmp digits : List Bool) :
    computer.step (parserCfg .second (bit :: input) m tmp digits) =
      some (parserCfg .second input m (bit :: tmp) digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clean, Multiplication.saveBit, Multiplication.clean, Addition.initial,
    MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem step_second_nil (m tmp digits : List Bool) :
    computer.step (parserCfg .second [] m tmp digits) =
      some (parserCfg .reverse [] m tmp digits) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clean, Multiplication.saveBit, Multiplication.clean, Addition.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem step_reverse_cons (bit : Bool) (m tmp digits : List Bool) :
    computer.step (parserCfg .reverse [] m (bit :: tmp) digits) =
      some (parserCfg .reverse [] m tmp (bit :: digits)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clean, Multiplication.saveBit, Multiplication.clean, Addition.initial,
    MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

theorem step_reverse_nil (m digits : List Bool) :
    computer.step (parserCfg .reverse [] m [] digits) =
      some (sourceCfg (Multiplication.cfg (some (.inr .loop)) [] [] [] [] m digits)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clean, Multiplication.saveBit, Multiplication.clean, Addition.initial,
    MachineFrame.update_left, sourceCfg, MachineFrame.cfg, Multiplication.cfg,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

def Runs (start finish : Config) (time : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[time] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

theorem first_exact (word input m tmp digits : List Bool) :
    Runs (parserCfg .first (Holant.Algebraic.frame word ++ input) m tmp digits)
      (parserCfg .second input (word.reverse ++ m) tmp digits) (word.length + 1) := by
  induction word generalizing m with
  | nil => simpa [Holant.Algebraic.frame] using Runs.one (step_delimiter input m tmp digits)
  | cons bit word ih =>
    have h := (Runs.one (step_first_cons bit (Holant.Algebraic.frame word ++ input) m tmp digits)).trans
      (ih (bit :: m))
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

theorem second_exact (word m tmp digits : List Bool) :
    Runs (parserCfg .second word m tmp digits)
      (parserCfg .reverse [] m (word.reverse ++ tmp) digits) (word.length + 1) := by
  induction word generalizing tmp with
  | nil => simpa using Runs.one (step_second_nil m tmp digits)
  | cons bit word ih =>
    have h := (Runs.one (step_second_cons bit word m tmp digits)).trans (ih (bit :: tmp))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem reverse_exact (tmp m digits : List Bool) :
    Runs (parserCfg .reverse [] m tmp digits)
      (sourceCfg (Multiplication.cfg (some (.inr .loop)) [] [] [] [] m (tmp.reverse ++ digits)))
      (tmp.length + 1) := by
  induction tmp generalizing digits with
  | nil => simpa using Runs.one (step_reverse_nil m digits)
  | cons bit tmp ih =>
    have h := (Runs.one (step_reverse_cons bit m tmp digits)).trans (ih (bit :: digits))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- The parser starts from the library's actual single-input configuration. -/
theorem parserCfg_init (input : List Bool) :
    parserCfg .first input [] [] [] = initList computer input := by
  dsimp [parserCfg, initList, clean, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

/-- All arithmetic and parser scratch storage is empty at the actual clean halt. -/
theorem sourceCfg_halt (output : List Bool) :
    sourceCfg (Multiplication.cfg none output [] [] [] [] []) = haltList computer output := by
  dsimp [sourceCfg, MachineFrame.cfg, Multiplication.cfg, haltList, computer, clean]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

theorem lift_multiplication {a b : Multiplication.Config} {time : ℕ}
    (h : Multiplication.Runs a b time) : Runs (sourceCfg a) (sourceCfg b) time := by
  unfold Runs sourceCfg
  change (fun d => d.bind (TM2.step (MachineFrame.program Multiplication.computer.m parser)))^[time]
    (some (MachineFrame.cfg a () (fun _ : Unit => []))) = _
  rw [MachineFrame.run_program]
  change ((fun c => c.bind Multiplication.computer.step)^[time] (some a)).map _ = _
  rw [h]
  rfl

/-- The exact complete transition count includes both parses, reversal, arithmetic
and cleanup. Nothing is delegated to a host-language word operation. -/
theorem encoded_exact (a b : ℕ) :
    Runs (initList computer (inputEncoding.encode (a, b)))
      (haltList computer (encodeNat (a * b)))
      ((encodeNat a).length + 2 * (encodeNat b).length + 3 +
        MultiplyBits.time (encodeNat a) (encodeNat b).reverse []) := by
  have h₁ := first_exact (encodeNat a).reverse (encodeNat b).reverse [] [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact (encodeNat b).reverse (encodeNat a) [] []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := reverse_exact (encodeNat b) (encodeNat a) []
  simp only [List.append_nil] at h₃
  have h₄ := lift_multiplication (Multiplication.compute_encodeNat_exact a b)
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  rw [sourceCfg_halt, parserCfg_init] at h
  change Runs (initList computer (inputEncoding.encode (a, b))) _ _ at h
  convert h using 1
  simp
  omega

/-- A concrete cubic bound for the actual finite binary multiplication machine. -/
noncomputable def multiplicationPolyTime :
    PolyTime inputEncoding encodingNatBool (fun p => p.1 * p.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := (Polynomial.X + 1) * (6 * ((Polynomial.X + 1) * (Polynomial.X + 2) + 3)) +
    3 * Polynomial.X + 3
  outputsFun p := by
    change TM2OutputsInTime computer (List.map id (inputEncoding.encode p))
      (some (List.map id (encodeNat (p.1 * p.2))))
      (((Polynomial.X + 1) * (6 * ((Polynomial.X + 1) * (Polynomial.X + 2) + 3)) +
        3 * Polynomial.X + 3).eval (inputEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := ((encodeNat p.1).length + 2 * (encodeNat p.2).length + 3 +
                MultiplyBits.time (encodeNat p.1) (encodeNat p.2).reverse [])
             evals_in_steps := encoded_exact p.1 p.2
             steps_le_m := ?_ }
    let L := (inputEncoding.encode p).length
    have hm : (encodeNat p.1).length ≤ L := by
      dsimp [L]; rw [EncodedAddition.inputEncoding_length]; omega
    have hn : (encodeNat p.2).length ≤ L := by
      dsimp [L]; rw [EncodedAddition.inputEncoding_length]; omega
    have ht := MultiplyBits.time_le (encodeNat p.1) (encodeNat p.2).reverse []
    simp only [List.length_reverse, List.length_nil, Nat.zero_add] at ht
    have hprod : ((encodeNat p.2).length + 1) * ((encodeNat p.1).length + 2) ≤
        (L + 1) * (L + 2) :=
      Nat.mul_le_mul (Nat.add_le_add_right hn 1) (Nat.add_le_add_right hm 2)
    have hlarge : ((encodeNat p.2).length + 1) *
          (6 * (((encodeNat p.2).length + 1) * ((encodeNat p.1).length + 2) + 3)) ≤
        (L + 1) * (6 * ((L + 1) * (L + 2) + 3)) :=
      Nat.mul_le_mul (Nat.add_le_add_right hn 1)
        (Nat.mul_le_mul_left 6 (Nat.add_le_add_right hprod 3))
    have hbound := le_trans ht hlarge
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one]
    change _ ≤ (L + 1) * (6 * ((L + 1) * (L + 2) + 3)) + 3 * L + 3
    omega
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem multiplication_inFP : InFP inputEncoding encodingNatBool (fun p => p.1 * p.2) :=
  ⟨multiplicationPolyTime⟩

theorem parser_budget (phase : Phase) : TM2Cost.budget (parser phase) ≤ 6 := by
  cases phase <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 8 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineFrame.program, MachineFrame.budget_stmt] using Multiplication.program_budget label
  | inr phase => exact le_trans (parser_budget phase) (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 7 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 11 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.EncodedMultiplication
