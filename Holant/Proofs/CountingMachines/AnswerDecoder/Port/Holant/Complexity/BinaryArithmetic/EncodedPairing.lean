import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.BinaryArithmetic.Pairing
import Holant.Complexity.BinaryArithmetic.EncodedAddition


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
open _root_.Holant.Complexity
open _root_.Holant.Complexity.BinaryArithmetic


/-! Faithfully serialized natural pairing. The two finite parsing loops feed the
actual comparison/square/add machine. Both parsing and every arithmetic, copy,
branch, cleanup and halting transition are charged. -/

namespace Holant.Complexity.BinaryArithmetic.EncodedPairing

open Turing Computability
open Turing.TM2.Stmt
open Pairing

abbrev inputEncoding := EncodedAddition.inputEncoding

abbrev K := Pairing.K ⊕ Unit
abbrev Label := Pairing.Label ⊕ Bool
abbrev Memory := Pairing.State × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

/-- The parser's only register is the existing optional-bit scratch field. -/
def saveBit (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), v.2)

def clear : Memory := (Pairing.initial, ())

/-- The first phase consumes a `true, bit` pair or the `false` delimiter.
The second phase consumes the remainder, then jumps to the compiled pairing machine. -/
def parser : Bool → Statement
  | false => pop (.inr ()) saveBit
      (branch (fun v => v.1.2.1.getD false)
        (pop (.inr ()) saveBit
          (push (.inl (.inl (.inl .left))) (fun v => v.1.2.1.getD false)
            (load (fun _ => clear) (goto (fun _ => .inr false)))))
        (load (fun _ => clear) (goto (fun _ => .inr true))))
  | true => pop (.inr ()) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl (.inl (.inl .right))) (fun v => v.1.2.1.getD false)
          (load (fun _ => clear) (goto (fun _ => .inr true))))
        (load (fun _ => clear) (goto (fun _ => .inl (Pairing.ph .compare)))))

abbrev computer : FinTM2 where
  K := K
  k₀ := .inr ()
  k₁ := .inl (.inl (.inl .out))
  Γ _ := Bool
  Λ := Label
  main := .inr false
  σ := Memory
  initialState := clear
  m := MachineFrame.program Pairing.program parser

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def parserCfg (phase : Bool) (input a b : List Bool) : Config :=
  ⟨some (.inr phase), clear, Sum.elim (Pairing.tapes a b [] [] [] [] [] []) (fun _ => input)⟩

def sourceCfg (c : Pairing.Config) : Config := MachineFrame.cfg c () (fun _ : Unit => [])

@[simp] theorem update_input (source : Pairing.K → List Bool) (input word : List Bool) :
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
    TM2.stepAux, saveBit, clear, Pairing.initial, Addition.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_delimiter (rest a b : List Bool) :
    computer.step (parserCfg false (false :: rest) a b) =
      some (parserCfg true rest a b) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Pairing.initial, Addition.initial,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_cons (x : Bool) (rest a b : List Bool) :
    computer.step (parserCfg true (x :: rest) a b) =
      some (parserCfg true rest a (x :: b)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Pairing.initial, Addition.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_nil (a b : List Bool) :
    computer.step (parserCfg true [] a b) =
      some (sourceCfg (Pairing.cfg (some (Pairing.ph .compare)) false a b [] [] [] [] [] [])) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Pairing.initial, Addition.initial, sourceCfg, MachineFrame.cfg, Pairing.cfg,
    Pairing.reset, Addition.reset]
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

/-- Exact preparation of the second operand and transfer to pairing control. -/
theorem second_exact (word a b : List Bool) :
    Runs (parserCfg true word a b)
      (sourceCfg (Pairing.cfg (some (Pairing.ph .compare)) false a (word.reverse ++ b) [] [] [] [] [] []))
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
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

/-- The final state is exactly mathlib's clean-output convention. -/
theorem sourceCfg_halt (output : List Bool) :
    sourceCfg (Pairing.cfg none false [] [] [] output [] [] [] []) = haltList computer output := by
  dsimp [sourceCfg, MachineFrame.cfg, Pairing.cfg, haltList, computer, clear, Pairing.reset, Pairing.initial, Addition.reset, Addition.initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

/-- The compiled source execution preserves every transition, including halt. -/
theorem lift_pairing {a b : Pairing.Config} {time : ℕ} (h : Pairing.Runs a b time) :
    Runs (sourceCfg a) (sourceCfg b) time := by
  unfold Runs sourceCfg
  change (fun d => d.bind (TM2.step (MachineFrame.program Pairing.program parser)))^[time]
    (some (MachineFrame.cfg a () (fun _ : Unit => []))) = _
  rw [MachineFrame.run_program]
  change ((fun c => c.bind Pairing.computer.step)^[time] (some a)).map _ = _
  rw [h]
  rfl

/-- All serialized-input transitions are counted against the real TM2 semantics. -/
theorem encoded_exact (a b : ℕ) :
    Runs (initList computer (inputEncoding.encode (a, b)))
      (haltList computer (encodeNat (Nat.pair a b)))
      ((encodeNat a).length + (encodeNat b).length +
        Pairing.time a b + 2) := by
  have h₁ := first_exact (encodeNat a).reverse (encodeNat b).reverse [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact (encodeNat b).reverse (encodeNat a) []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := lift_pairing (Pairing.compute_encodeNat_exact a b)
  have h := (h₁.trans h₂).trans h₃
  rw [sourceCfg_halt] at h
  rw [parserCfg_init] at h
  change Runs (initList computer (inputEncoding.encode (a, b))) _ _ at h
  convert h using 1
  simp
  omega


/-- A genuine finite Boolean-stack polynomial-time witness for literal Nat.pair. -/
noncomputable def pairingPolyTime :
    PolyTime inputEncoding encodingNatBool (fun p => Nat.pair p.1 p.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := (Polynomial.X + 1) * (6 * ((Polynomial.X + 1) * (Polynomial.X + 2) + 3)) +
    2 * ((Polynomial.X + 1) * (Polynomial.X + 2)) + 12 * Polynomial.X + 22
  outputsFun p := by
    change TM2OutputsInTime computer (List.map id (inputEncoding.encode p))
      (some (List.map id (encodeNat (Nat.pair p.1 p.2))))
      (((Polynomial.X + 1) * (6 * ((Polynomial.X + 1) * (Polynomial.X + 2) + 3)) +
        2 * ((Polynomial.X + 1) * (Polynomial.X + 2)) + 12 * Polynomial.X + 22).eval
        (inputEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := (encodeNat p.1).length + (encodeNat p.2).length + Pairing.time p.1 p.2 + 2
             evals_in_steps := encoded_exact p.1 p.2
             steps_le_m := ?_ }
    let L := (inputEncoding.encode p).length
    have ha : (encodeNat p.1).length ≤ L := by
      dsimp [L]; rw [EncodedAddition.inputEncoding_length]; omega
    have hb : (encodeNat p.2).length ≤ L := by
      dsimp [L]; rw [EncodedAddition.inputEncoding_length]; omega
    have ht := Pairing.time_le p.1 p.2 L ha hb
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_one]
    change _ ≤ (L + 1) * (6 * ((L + 1) * (L + 2) + 3)) +
      2 * ((L + 1) * (L + 2)) + 12 * L + 22
    omega
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem pairing_inFP : InFP inputEncoding encodingNatBool (fun p => Nat.pair p.1 p.2) :=
  ⟨pairingPolyTime⟩

theorem parser_budget (phase : Bool) : TM2Cost.budget (parser phase) ≤ 6 := by
  cases phase <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 9 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineFrame.program, MachineFrame.budget_stmt] using Pairing.program_budget label
  | inr phase => exact le_trans (parser_budget phase) (by decide)

@[simp] theorem stack_count : Fintype.card computer.K = 9 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 24 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 18 := by decide

end Holant.Complexity.BinaryArithmetic.EncodedPairing

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
