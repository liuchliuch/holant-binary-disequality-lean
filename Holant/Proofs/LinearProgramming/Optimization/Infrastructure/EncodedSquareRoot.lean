import Holant.Complexity.BinaryArithmetic.SquareRoot
import Holant.Complexity.MachineFrame

/-! Canonical binary square root from one ordinary natural encoding. Input bits
are paired from the low end, reversed as pairs, and padded only at an odd high
end. Every parser transition and arithmetic transition is counted. -/

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Infrastructure.EncodedSquareRoot

open Turing Computability Holant.Complexity Holant.Complexity.BinaryArithmetic
open Turing.TM2.Stmt
open SquareRootBits

abbrev K := SquareRoot.Stack ⊕ Unit
abbrev Label := SquareRoot.Label ⊕ Unit
abbrev Memory := SquareRoot.State × Unit
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

def saveFirst (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, bit, v.1.2.2), ())
def saveSecond (v : Memory) (bit : Option Bool) : Memory := ((v.1.1, v.1.2.1, bit), ())
def clear : Memory := (SquareRoot.initial, ())
def again : Statement := load (fun _ => clear) (goto (fun _ => .inr ()))

/-- Pop at most two source bits; absent high bits are zero padded. -/
def parser (_ : Unit) : Statement :=
  pop (.inr ()) saveFirst
    (branch (fun v => v.1.2.1.isSome)
      (pop (.inr ()) saveSecond
        (push (.inl .input) (fun v => v.1.2.1.getD false)
          (push (.inl .input) (fun v => v.1.2.2.getD false) again)))
      (load (fun _ => clear) (goto (fun _ => .inl .next))))

abbrev computer (out : Bool) : FinTM2 where
  K := K
  k₀ := .inr ()
  k₁ := .inl (if out then .remainder else .divisor)
  Γ _ := Bool
  Λ := Label
  main := .inr ()
  σ := Memory
  initialState := clear
  m := MachineFrame.program (SquareRoot.program (some out)) parser

instance finiteAlphabet (out : Bool) (k : (computer out).K) :
    Fintype ((computer out).Γ k) := inferInstanceAs (Fintype Bool)

def parserCfg (input i : List Bool) : Config :=
  ⟨some (.inr ()), clear, Sum.elim (SquareRoot.tapes i [] [] [] [] [] []) (fun _ => input)⟩

def sqrtCfg (c : SquareRoot.Config) : Config := MachineFrame.cfg c () (fun _ : Unit => [])

@[simp] theorem update_input (source : SquareRoot.Stack → List Bool) (input word : List Bool) :
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

@[simp] theorem step_pair (out lo hi : Bool) (rest i : List Bool) :
    (computer out).step (parserCfg (lo :: hi :: rest) i) =
      some (parserCfg rest (hi :: lo :: i)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveFirst, saveSecond, clear, again, SquareRoot.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_single (out lo : Bool) (i : List Bool) :
    (computer out).step (parserCfg [lo] i) = some (parserCfg [] (false :: lo :: i)) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveFirst, saveSecond, clear, again, SquareRoot.initial, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

@[simp] theorem step_nil (out : Bool) (i : List Bool) :
    (computer out).step (parserCfg [] i) =
      some (sqrtCfg (SquareRoot.cfg (some .next) false i [] [] [] [] [] [])) := by
  simp [FinTM2.step, TM2.step, computer, MachineFrame.program, parserCfg, parser,
    TM2.stepAux, saveFirst, saveSecond, clear, SquareRoot.initial, sqrtCfg, MachineFrame.cfg,
    SquareRoot.cfg, SquareRoot.reset, MachineFrame.update_left,
    -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
  congr 2

/-- Explicit bit pairing and digit reversal from the actual binary input. -/
theorem parser_exact (out : Bool) (word i : List Bool) :
    Runs out (parserCfg word i)
      (sqrtCfg (SquareRoot.cfg (some .next) false
        (SquareRoot.digitStream (groupBits word).reverse ++ i) [] [] [] [] [] []))
      ((groupBits word).length + 1) := by
  induction word using groupBits.induct generalizing i with
  | case1 => simpa [groupBits] using Runs.one (step_nil out i)
  | case2 lo =>
    have h := (Runs.one (step_single out lo i)).trans (Runs.one (step_nil out (false :: lo :: i)))
    simpa [groupBits, SquareRoot.digitStream] using h
  | case3 lo hi rest ih =>
    have h := (Runs.one (step_pair out lo hi rest i)).trans (ih (hi :: lo :: i))
    simpa [groupBits, List.reverse_cons, List.append_assoc] using h

/-- The parser is initialized by the standard single-input machine convention. -/
theorem parserCfg_init (out : Bool) (input : List Bool) :
    parserCfg input [] = initList (computer out) input := by
  dsimp [parserCfg, initList, clear, computer]
  congr 1
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k; rfl

theorem sqrtCfg_halt (out : Bool) (output : List Bool) :
    sqrtCfg (SquareRoot.finalCfg out output) = haltList (computer out) output := by
  cases out <;> dsimp [sqrtCfg, MachineFrame.cfg, SquareRoot.finalCfg, SquareRoot.cfg,
    haltList, computer, clear, SquareRoot.reset, SquareRoot.initial]
  all_goals
    congr 1
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k; rfl

/-- Structural embedding preserves each finite arithmetic transition. -/
theorem lift_sqrt {out : Bool} {a b : SquareRoot.Config} {time : ℕ}
    (h : SquareRoot.Runs (some out) a b time) : Runs out (sqrtCfg a) (sqrtCfg b) time := by
  unfold Runs sqrtCfg
  change (fun d => d.bind (TM2.step (MachineFrame.program (SquareRoot.program (some out)) parser)))^[time]
    (some (MachineFrame.cfg a () (fun _ : Unit => []))) = _
  rw [MachineFrame.run_program]
  change ((fun c => c.bind (SquareRoot.computer (some out)).step)^[time] (some a)).map _ = _
  rw [h]
  rfl

/-- Exact canonical root/square remainder with a completely clean final tape. -/
theorem encoded_exact (out : Bool) (n : ℕ) :
    Runs out (initList (computer out) (encodeNat n))
      (haltList (computer out) (encodeNat (if out then n - Nat.sqrt n ^ 2 else Nat.sqrt n)))
      (SquareRoot.computeTime out (groupBits (encodeNat n)).reverse +
        (groupBits (encodeNat n)).length + 1) := by
  have h₁ := parser_exact out (encodeNat n) []
  simp only [List.append_nil] at h₁
  have h₂ := lift_sqrt (SquareRoot.compute_encodeNat_exact out n)
  have h := h₁.trans h₂
  rw [sqrtCfg_halt, parserCfg_init] at h
  convert h using 1

theorem groupBits_length_le (bits : List Bool) : (groupBits bits).length ≤ bits.length := by
  induction bits using groupBits.induct with
  | case1 => simp [groupBits]
  | case2 lo => simp [groupBits]
  | case3 lo hi rest ih => simp only [groupBits, List.length_cons]; omega

/-- Runtime is polynomial in the supplied binary length, never the numeric value. -/
theorem encoded_time_le (out : Bool) (bits : List Bool) :
    SquareRoot.computeTime out (groupBits bits).reverse + (groupBits bits).length + 1 ≤
      6 * bits.length ^ 2 + 14 * bits.length + 3 := by
  have ht := SquareRoot.computeTime_le out (groupBits bits).reverse
  simp only [List.length_reverse] at ht
  have hg := groupBits_length_le bits
  have hs : (groupBits bits).length ^ 2 ≤ bits.length ^ 2 := Nat.pow_le_pow_left hg 2
  omega

noncomputable def squareRootRemainderPolyTime (out : Bool) :
    PolyTime encodingNatBool encodingNatBool (fun n => if out then n - Nat.sqrt n ^ 2 else Nat.sqrt n) where
  tm := computer out
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X ^ 2 + 14 * Polynomial.X + 3
  outputsFun n := by
    change TM2OutputsInTime (computer out) (List.map id (encodeNat n))
      (some (List.map id (encodeNat (if out then n - Nat.sqrt n ^ 2 else Nat.sqrt n))))
      ((6 * Polynomial.X ^ 2 + 14 * Polynomial.X + 3).eval (encodeNat n).length)
    rw [List.map_id, List.map_id]
    refine { steps := SquareRoot.computeTime out (groupBits (encodeNat n)).reverse +
               (groupBits (encodeNat n)).length + 1
             evals_in_steps := encoded_exact out n
             steps_le_m := ?_ }
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow] using encoded_time_le out (encodeNat n)
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

noncomputable def squareRootPolyTime : PolyTime encodingNatBool encodingNatBool Nat.sqrt :=
  squareRootRemainderPolyTime false

noncomputable def squareRemainderPolyTime :
    PolyTime encodingNatBool encodingNatBool (fun n => n - Nat.sqrt n ^ 2) :=
  squareRootRemainderPolyTime true

theorem squareRoot_inFP : InFP encodingNatBool encodingNatBool Nat.sqrt := ⟨squareRootPolyTime⟩
theorem squareRemainder_inFP : InFP encodingNatBool encodingNatBool (fun n => n - Nat.sqrt n ^ 2) :=
  ⟨squareRemainderPolyTime⟩

theorem parser_budget : TM2Cost.budget (parser ()) ≤ 8 := by decide

theorem program_budget (out : Bool) (label : Label) : TM2Cost.budget ((computer out).m label) ≤ 17 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineFrame.program, MachineFrame.budget_stmt] using
      SquareRoot.program_budget (some out) label
  | inr label => cases label; exact parser_budget.trans (by decide)

@[simp] theorem stack_count (out : Bool) : Fintype.card (computer out).K = 8 := by cases out <;> decide
@[simp] theorem label_count (out : Bool) : Fintype.card (computer out).Λ = 10 := by cases out <;> decide
@[simp] theorem state_count (out : Bool) : Fintype.card (computer out).σ = 18 := by cases out <;> decide

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Infrastructure.EncodedSquareRoot
