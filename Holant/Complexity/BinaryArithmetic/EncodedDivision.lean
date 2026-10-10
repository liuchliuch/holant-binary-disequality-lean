import Holant.Complexity.BinaryArithmetic.Division
import Holant.Complexity.BinaryArithmetic.EncodedAddition

/-!
# Serialized binary quotient and remainder in genuine polynomial time

Both machines consume exactly the established faithful binary pair codec. Three
finite parser phases decode the framed dividend and divisor and explicitly restore
the dividend's MSB-first processing order. The proved long-division core is then
structurally embedded. Every parsing, arithmetic and cleanup transition is counted;
outputs are canonical natural encodings, including the divisor-zero convention.
-/

namespace Holant.Complexity.BinaryArithmetic.EncodedDivision

open Turing Computability
open Turing.TM2.Stmt

abbrev inputEncoding := EncodedAddition.inputEncoding
abbrev K := Division.Stack ⊕ Unit

inductive ParseLabel
  | first | second | reverse
  deriving DecidableEq
instance : Fintype ParseLabel := ⟨{.first, .second, .reverse}, by intro k; cases k <;> simp⟩

abbrev Label := Division.Label ⊕ ParseLabel
abbrev Memory := Division.State × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

def saveBit (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), v.2)
def clear : Memory := (Division.initial, ())
def again (label : ParseLabel) : Statement := load (fun _ => clear) (goto (fun _ => .inr label))

/-- The arithmetic scratch stack stages the dividend, and is emptied before entry. -/
def parser : ParseLabel → Statement
  | .first => pop (.inr ()) saveBit
      (branch (fun v => v.1.2.1.getD false)
        (pop (.inr ()) saveBit
          (push (.inl .divisorRev) (fun v => v.1.2.1.getD false) (again .first)))
        (again .second))
  | .second => pop (.inr ()) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .divisor) (fun v => v.1.2.1.getD false) (again .second))
        (again .reverse))
  | .reverse => pop (.inl .divisorRev) saveBit
      (branch (fun v => v.1.2.1.isSome)
        (push (.inl .input) (fun v => v.1.2.1.getD false) (again .reverse))
        (load (fun _ => clear) (goto (fun _ => .inl .start))))

abbrev computer (out : Bool) : FinTM2 where
  K := K
  k₀ := .inr ()
  k₁ := .inl (if out then .remainder else .quotient)
  Γ _ := Bool
  Λ := Label
  main := .inr .first
  σ := Memory
  initialState := clear
  m := MachineFrame.program (Division.program out) parser

instance finiteAlphabet (out : Bool) (k : (computer out).K) :
    Fintype ((computer out).Γ k) := inferInstanceAs (Fintype Bool)

def parserCfg (phase : ParseLabel) (input stage d i : List Bool) : Config :=
  ⟨some (.inr phase), clear, Sum.elim (Division.tapes i d [] stage [] [] []) (fun _ => input)⟩

def dividerCfg (c : Division.Config) : Config := MachineFrame.cfg c () (fun _ : Unit => [])

@[simp] theorem update_input (source : Division.Stack → List Bool) (input word : List Bool) :
    Function.update (Sum.elim source (fun _ : Unit => input)) (.inr ()) word =
      Sum.elim source (fun _ : Unit => word) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => cases k; simp

def Runs (out : Bool) (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind (computer out).step)^[n] (some start) = some finish

theorem Runs.one {out : Bool} {a b : Config} (h : (computer out).step a = some b) : Runs out a b 1 := h

theorem Runs.trans {out : Bool} {a b c : Config} {n m : ℕ} (h : Runs out a b n) (h' : Runs out b c m) :
    Runs out a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

@[simp] theorem step_first_cons (out x : Bool) (rest stage d i : List Bool) :
    (computer out).step (parserCfg .first (true :: x :: rest) stage d i) =
      some (parserCfg .first rest (x :: stage) d i) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_delimiter (out : Bool) (rest stage d i : List Bool) :
    (computer out).step (parserCfg .first (false :: rest) stage d i) =
      some (parserCfg .second rest stage d i) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_cons (out x : Bool) (rest stage d i : List Bool) :
    (computer out).step (parserCfg .second (x :: rest) stage d i) =
      some (parserCfg .second rest stage (x :: d) i) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_second_nil (out : Bool) (stage d i : List Bool) :
    (computer out).step (parserCfg .second [] stage d i) =
      some (parserCfg .reverse [] stage d i) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_reverse_cons (out x : Bool) (stage d i : List Bool) :
    (computer out).step (parserCfg .reverse [] (x :: stage) d i) =
      some (parserCfg .reverse [] stage d (x :: i)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, again, Division.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_reverse_nil (out : Bool) (d i : List Bool) :
    (computer out).step (parserCfg .reverse [] [] d i) =
      some (dividerCfg (Division.cfg (some .start) false i d [] [] [] [] [])) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveBit, clear, Division.initial, dividerCfg, MachineFrame.cfg,
    Division.cfg, Division.reset, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

/-- Decode the framed first operand without changing the following stream. -/
theorem first_exact (out : Bool) (word rest stage d i : List Bool) :
    Runs out (parserCfg .first (Holant.Algebraic.frame word ++ rest) stage d i)
      (parserCfg .second rest (word.reverse ++ stage) d i) (word.length + 1) := by
  induction word generalizing stage with
  | nil => simpa [Holant.Algebraic.frame] using Runs.one (step_delimiter out rest stage d i)
  | cons bit word ih =>
    have h := (Runs.one (step_first_cons out bit (Holant.Algebraic.frame word ++ rest) stage d i)).trans
      (ih (bit :: stage))
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

/-- Decode the second operand into the little-endian divisor stack. -/
theorem second_exact (out : Bool) (word stage d i : List Bool) :
    Runs out (parserCfg .second word stage d i)
      (parserCfg .reverse [] stage (word.reverse ++ d) i) (word.length + 1) := by
  induction word generalizing d with
  | nil => simpa using Runs.one (step_second_nil out stage d i)
  | cons bit word ih =>
    have h := (Runs.one (step_second_cons out bit word stage d i)).trans (ih (bit :: d))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- Explicitly restore the dividend's MSB-first processing order. -/
theorem reverse_exact (out : Bool) (stage d i : List Bool) :
    Runs out (parserCfg .reverse [] stage d i)
      (dividerCfg (Division.cfg (some .start) false (stage.reverse ++ i) d [] [] [] [] []))
      (stage.length + 1) := by
  induction stage generalizing i with
  | nil => simpa using Runs.one (step_reverse_nil out d i)
  | cons bit stage ih =>
    have h := (Runs.one (step_reverse_cons out bit stage d i)).trans (ih (bit :: i))
    simpa [List.reverse_cons, List.append_assoc] using h

/-- The parser begins at the actual single-input initialization convention. -/
theorem parserCfg_init (out : Bool) (input : List Bool) :
    parserCfg .first input [] [] [] = initList (computer out) input := by
  dsimp [parserCfg, initList, clear, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

/-- Both selected results use the actual clean-output halt convention. -/
theorem dividerCfg_halt (out : Bool) (output : List Bool) :
    dividerCfg (Division.finalCfg out output) = haltList (computer out) output := by
  cases out <;> dsimp [dividerCfg, MachineFrame.cfg, Division.finalCfg, Division.cfg,
    haltList, computer, clear, Division.reset, Division.initial]
  all_goals
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k; rfl

/-- Structural embedding preserves every real long-division transition. -/
theorem lift_division {out : Bool} {a b : Division.Config} {time : ℕ} (h : Division.Runs out a b time) :
    Runs out (dividerCfg a) (dividerCfg b) time := by
  unfold Runs dividerCfg
  change (fun d => d.bind (TM2.step (MachineFrame.program (Division.program out) parser)))^[time]
    (some (MachineFrame.cfg a () (fun _ : Unit => []))) = _
  rw [MachineFrame.run_program]
  change ((fun c => c.bind (Division.computer out).step)^[time] (some a)).map _ = _
  rw [h]
  rfl

/-- Every serialized-input, arithmetic and cleanup transition is retained. -/
theorem encoded_exact (out : Bool) (a b : ℕ) :
    Runs out (initList (computer out) (inputEncoding.encode (a,b)))
      (haltList (computer out) (encodeNat (if out then a % b else a / b)))
      (Division.computeTime out (encodeNat a).reverse (encodeNat b) +
        2 * (encodeNat a).length + (encodeNat b).length + 3) := by
  have h₁ := first_exact out (encodeNat a).reverse (encodeNat b).reverse [] [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact out (encodeNat b).reverse (encodeNat a) [] []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := reverse_exact out (encodeNat a) (encodeNat b) []
  simp only [List.append_nil] at h₃
  have h₄ := lift_division (Division.compute_encodeNat_exact out a b)
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  rw [dividerCfg_halt, parserCfg_init] at h
  change Runs out (initList (computer out) (inputEncoding.encode (a,b))) _ _ at h
  convert h using 1
  simp
  omega

/-- Polynomial-time canonical natural quotient/remainder from one faithful bit stream. -/
noncomputable def quotientRemainderPolyTime (out : Bool) :
    PolyTime inputEncoding encodingNatBool (fun p => if out then p.1 % p.2 else p.1 / p.2) where
  tm := computer out
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 3 * Polynomial.X ^ 2 + 10 * Polynomial.X + 7
  outputsFun p := by
    change TM2OutputsInTime (computer out) (List.map id (inputEncoding.encode p))
      (some (List.map id (encodeNat (if out then p.1 % p.2 else p.1 / p.2))))
      ((3 * Polynomial.X ^ 2 + 10 * Polynomial.X + 7).eval (inputEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := Division.computeTime out (encodeNat p.1).reverse (encodeNat p.2) +
               2 * (encodeNat p.1).length + (encodeNat p.2).length + 3
             evals_in_steps := encoded_exact out p.1 p.2
             steps_le_m := ?_ }
    have hb := Division.computeTime_le out (encodeNat p.1).reverse (encodeNat p.2)
    simp only [List.length_reverse] at hb
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow, EncodedAddition.inputEncoding_length]
    let n := 2 * (encodeNat p.1).length + (encodeNat p.2).length + 1
    have ha : (encodeNat p.1).length ≤ n := by dsimp [n]; omega
    have hab : (encodeNat p.1).length + (encodeNat p.2).length ≤ n := by dsimp [n]; omega
    have hp : (3 * ((encodeNat p.1).length + (encodeNat p.2).length) + 7) * (encodeNat p.1).length ≤
        (3 * n + 7) * n := Nat.mul_le_mul (by omega) ha
    change _ ≤ 3 * n ^ 2 + 10 * n + 7
    have hlength : 3 * (encodeNat p.1).length + 2 * (encodeNat p.2).length ≤ 2 * n := by
      dsimp [n]; omega
    calc
      _ ≤ (3 * n + 7) * n + 2 * n + 7 := by omega
      _ ≤ 3 * n ^ 2 + 10 * n + 7 := by
        simp only [pow_two, Nat.add_mul, Nat.mul_assoc]
        omega
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

noncomputable def divisionPolyTime : PolyTime inputEncoding encodingNatBool (fun p => p.1 / p.2) :=
  quotientRemainderPolyTime false

noncomputable def remainderPolyTime : PolyTime inputEncoding encodingNatBool (fun p => p.1 % p.2) :=
  quotientRemainderPolyTime true

theorem division_inFP : InFP inputEncoding encodingNatBool (fun p => p.1 / p.2) := ⟨divisionPolyTime⟩
theorem remainder_inFP : InFP inputEncoding encodingNatBool (fun p => p.1 % p.2) := ⟨remainderPolyTime⟩

theorem parser_budget (label : ParseLabel) : TM2Cost.budget (parser label) ≤ 6 := by
  cases label <;> decide

theorem program_budget (out : Bool) (label : Label) : TM2Cost.budget ((computer out).m label) ≤ 12 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineFrame.program, MachineFrame.budget_stmt] using
      Division.program_budget out label
  | inr label => exact (parser_budget label).trans (by decide)

@[simp] theorem stack_count (out : Bool) : Fintype.card (computer out).K = 8 := by cases out <;> decide
@[simp] theorem label_count (out : Bool) : Fintype.card (computer out).Λ = 13 := by cases out <;> decide
@[simp] theorem state_count (out : Bool) : Fintype.card (computer out).σ = 18 := by cases out <;> decide

end Holant.Complexity.BinaryArithmetic.EncodedDivision
