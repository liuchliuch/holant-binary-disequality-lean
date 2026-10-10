import Holant.Complexity.IntegerArithmetic.CarryProtocol
import Holant.Complexity.GraphPreprocessing.Primitive
import Holant.Complexity.BinaryCompose.Interface
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Materializing physical unary graph coordinates as canonical binary words

Every counter token invokes the previously proved returning binary carry loop.
The actual finite machine consumes tokens, increments the destination bit stack,
and restores its scratch stack. There is no natural-valued register or free
conversion opcode. Its clean-input instance is a uniform Boolean-stack
`BinaryCompose.Computes` witness with a quadratic input-bit bound.
-/
namespace Holant.Complexity.GraphPreprocessing.UnaryBinary
open Turing Computability BinaryArithmetic IntegerArithmetic CarryProtocol
open Turing.TM2.Stmt

def loopStmt : Statement (Fin 3) (Fin 4) :=
  pop 0 saveBit
    (branch (fun v => v.1.1.2.1.isSome)
      (load clearBit (goto (fun _ => 1)))
      (load clearBit (goto (fun _ => 3))))

abbrev machine : BinaryCompose.Machine where
  K := Fin 3
  input := 0
  output := 1
  Label := Fin 4
  main := 0
  State := Memory
  initial := clean (false, false)
  program label := if label = 0 then loopStmt
    else if label = 1 then incrementStmt 1 2 1 2
    else if label = 2 then restoreStmt 1 2 2 (fun _ => 0) else .halt

def tapes (tokens word scratch : List Bool) : Fin 3 → List Bool := ![tokens, word, scratch]
def config (label : Fin 4) (tokens word scratch : List Bool) : machine.Config :=
  cfg label (false, false) (tapes tokens word scratch)

def Runs (a b : machine.Config) (n : ℕ) : Prop :=
  (fun c => c.bind machine.computer.step)^[n] (some a) = some b

theorem Runs.one {a b : machine.Config} (h : machine.computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : machine.Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

private theorem at_increment : ExecutesAt machine.computer.step (1 : Fin 4) (incrementStmt 1 2 1 2) := by intro state tapes; rfl
private theorem at_restore : ExecutesAt machine.computer.step (2 : Fin 4) (restoreStmt 1 2 2 (fun _ => 0)) := by intro state tapes; rfl

theorem loop_cons (bit : Bool) (tokens word : List Bool) :
    machine.computer.step (config 0 (bit :: tokens) word []) = some (config 1 tokens word []) := by
  simp [FinTM2.step, TM2.step, machine, loopStmt, config, cfg, TM2.stepAux, saveBit, clearBit,
    clean, Multiplication.saveBit, Multiplication.clean, Addition.initial, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem loop_nil (word : List Bool) :
    machine.computer.step (config 0 [] word []) = some (config 3 [] word []) := by
  simp [FinTM2.step, TM2.step, machine, loopStmt, config, cfg, TM2.stepAux, saveBit, clearBit,
    clean, Multiplication.saveBit, Multiplication.clean, Addition.initial, tapes]
  congr 2
  funext k
  fin_cases k <;> rfl

theorem increment_exact (tokens word : List Bool) :
    Runs (config 1 tokens word []) (config 0 tokens (increment word) []) (2 * (carryCount word + 1)) := by
  have h := increment_exact_frame (1 : Fin 3) 2 (by decide) machine.computer.step 1 2 (fun _ => 0)
    at_increment at_restore (false, false) (tapes tokens [] []) word
  change Runs _ _ _ at h
  convert h using 1 <;> unfold config <;> congr 1 <;> funext k <;> fin_cases k <;> rfl

/-- A mathematical record of the destination word; not a running instruction. -/
def added (word : List Bool) : ℕ → List Bool
  | 0 => word
  | n + 1 => added (increment word) n

def ticks (word : List Bool) : ℕ → ℕ
  | 0 => 1
  | n + 1 => ticks (increment word) n + (2 * (carryCount word + 1) + 1)

/-- Exact execution on arbitrary physical token and destination bit words. -/
theorem convert_word_exact (tokens word : List Bool) :
    Runs (config 0 tokens word []) (config 3 [] (added word tokens.length) []) (ticks word tokens.length) := by
  induction tokens generalizing word with
  | nil => exact Runs.one (loop_nil word)
  | cons bit tokens ih =>
    have first := (Runs.one (loop_cons bit tokens word)).trans (increment_exact tokens word)
    exact first.trans (ih (increment word))

theorem added_encodeNat (n k : ℕ) : added (encodeNat n) k = encodeNat (n + k) := by
  induction k generalizing n with
  | zero => simp [added]
  | succ k ih => simp [added, increment_encodeNat, ih, Nat.add_assoc, Nat.add_comm 1 k]

/-- Unary magnitude is bounded by physical input tokens, while carry lengths
increase by at most one bit per actual token. This also covers malformed words. -/
theorem ticks_le (word : List Bool) (k : ℕ) :
    ticks word k ≤ (k + 1) * (2 * (word.length + k) + 3) := by
  induction k generalizing word with
  | zero => simp [ticks]
  | succ k ih =>
    have ht := ih (increment word)
    have hc := carryCount_le word
    have hl := increment_length_le word
    have hm := Nat.mul_le_mul_left (k + 1) (show
      2 * ((increment word).length + k) + 3 ≤ 2 * (word.length + (k + 1)) + 3 by omega)
    simp only [ticks] at *
    nlinarith

theorem convert_exact (tokens : List Bool) (n : ℕ) :
    Runs (config 0 tokens (encodeNat n) []) (config 3 [] (encodeNat (n + tokens.length)) [])
      (ticks (encodeNat n) tokens.length) := by
  simpa only [added_encodeNat] using convert_word_exact tokens (encodeNat n)

def convert_correct (tokens : List Bool) (n : ℕ) :
    StateTransition.EvalsToInTime machine.computer.step (config 0 tokens (encodeNat n) [])
      (some (config 3 [] (encodeNat (n + tokens.length)) []))
      ((tokens.length + 1) * (2 * ((encodeNat n).length + tokens.length) + 3)) where
  steps := ticks (encodeNat n) tokens.length
  evals_in_steps := convert_exact tokens n
  steps_le_m := ticks_le _ _

/-- Only true-token words belong to the unary natural codec. -/
def unaryEncoding : Encoding ℕ Bool where
  encode n := List.replicate n true
  decode word := if word.all id then some word.length else none
  decode_encode n := by simp

theorem initial_eq (tokens : List Bool) :
    config 0 tokens [] [] = initList machine.computer tokens := by
  rw [BinaryCompose.Machine.init_eq]
  unfold config cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem halt_step (word : List Bool) :
    machine.computer.step (config 3 [] word []) = some (haltList machine.computer word) := by
  rw [BinaryCompose.Machine.halt_eq]
  dsimp [FinTM2.step, TM2.step, machine, config, cfg, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Clean uniform binary-stack conversion of a real unary input to canonical bits. -/
noncomputable def computes : BinaryCompose.Computes unaryEncoding encodingNatBool id where
  machine := machine
  time := 2 * Polynomial.X^2 + 5 * Polynomial.X + 4
  outputs n := by
    have first := convert_exact (List.replicate n true) 0
    change Runs (config 0 (List.replicate n true) [] [])
      (config 3 [] (encodeNat (0 + (List.replicate n true).length)) []) _ at first
    simp only [List.length_replicate, Nat.zero_add, initial_eq] at first
    have run := first.trans (Runs.one (halt_step (encodeNat n)))
    refine { steps := 1 + ticks [] n
             evals_in_steps := run
             steps_le_m := ?_ }
    have h := ticks_le [] n
    simp only [unaryEncoding, List.length_replicate, List.length_nil, Nat.zero_add] at *
    simp
    nlinarith

theorem program_budget (label : Fin 4) : TM2Cost.budget (machine.program label) ≤ 7 := by
  fin_cases label <;> decide

/-- Actual elementary execution cost, not an arithmetic-operation annotation. -/
theorem bit_cost (tokens word : List Bool) :
    (Primitive.run machine.program (ticks word tokens.length) (some (config 0 tokens word []))).2 =
      some (config 3 [] (added word tokens.length) []) ∧
    (Primitive.run machine.program (ticks word tokens.length) (some (config 0 tokens word []))).1 ≤
      7 * ((tokens.length + 1) * (2 * (word.length + tokens.length) + 3)) := by
  have h := Primitive.execution_cost machine.program 7 program_budget _ _ _ (convert_word_exact tokens word)
  exact ⟨h.1, le_trans h.2 (Nat.mul_le_mul_left 7 (ticks_le word tokens.length))⟩

end Holant.Complexity.GraphPreprocessing.UnaryBinary
