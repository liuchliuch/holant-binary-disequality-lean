import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.IntegerArithmetic.AdditionBits
import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.IntegerArithmetic.NormalizeProtocol
import Holant.Proofs.CountingMachines.AnswerDecoder.Port.Holant.Complexity.IntegerArithmetic.Multiplication


namespace Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
open _root_.Holant.Complexity
open _root_.Holant.Complexity.BinaryArithmetic
open _root_.Holant.Complexity.IntegerArithmetic


/-! Actual signed addition: equal signs invoke the carry-adder; opposite signs
compute both borrow differences, discard the unused buffer, normalize, and
remove the positive-result parity offset by an actual decrement. -/

namespace Holant.Complexity.IntegerArithmetic.Addition
open Turing Computability BinaryArithmetic
open Turing.TM2.Stmt
abbrev K := IntegerArithmetic.Multiplication.K
abbrev Signs := CarryProtocol.Signs
abbrev Memory := CarryProtocol.Memory
abbrev inputStack : K := .inr ()
abbrev aStack : K := .inl (.inl .left)
abbrev bStack : K := .inl (.inl .right)
abbrev wStack : K := .inl (.inl .work)
abbrev rStack : K := .inl (.inr false)
abbrev outStack : K := .inl (.inl .out)

inductive Phase
  | first | second | inspect | columns | clearF | clearR | trimF | reverseF
  | trimR | reverseR | finish | dec | restoreDec | halt
  deriving DecidableEq
instance : Fintype Phase := ⟨{.first, .second, .inspect, .columns, .clearF, .clearR, .trimF,
  .reverseF, .trimR, .reverseR, .finish, .dec, .restoreDec, .halt}, by intro p; cases p <;> simp⟩
abbrev CoreLabel := Bool ⊕ Empty
abbrev Label := CoreLabel ⊕ Phase
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

def coreOutside (e : Empty) : TM2.Stmt (fun _ : BinaryArithmetic.Multiplication.K => Bool)
    CoreLabel BinaryArithmetic.Multiplication.Memory := nomatch e
def coreProgram := MachineFrame.program BinaryArithmetic.Addition.program coreOutside

def initial : Memory := CarryProtocol.clean (false, false)
def ret (_ : Signs) : Phase := .halt

def columns : Statement :=
  pop aStack CarryProtocol.saveBit
    (pop bStack (fun v bit => (((v.1.1.1, v.1.1.2.1, bit), v.1.2), v.2))
      (branch (fun v => v.1.1.2.1.isSome || v.1.1.2.2.isSome)
        (push wStack (fun v => digitDiff v.1.1.1 (v.1.1.2.1.getD false) (v.1.1.2.2.getD false))
          (push rStack (fun v => digitDiff v.2.1 (v.1.1.2.2.getD false) (v.1.1.2.1.getD false))
            (load (fun v => ((BinaryArithmetic.Addition.reset
                (digitBorrow v.1.1.1 (v.1.1.2.1.getD false) (v.1.1.2.2.getD false)), ()),
              (digitBorrow v.2.1 (v.1.1.2.2.getD false) (v.1.1.2.1.getD false), v.2.2)))
              (goto (fun _ => .inr .columns)))))
        (branch (fun v => v.1.1.1)
          (load (fun v => CarryProtocol.clean (!v.2.2, false)) (goto (fun _ => .inr .clearF)))
          (load (fun v => CarryProtocol.clean (v.2.2, false)) (goto (fun _ => .inr .clearR))))))

def outside : Phase → Statement
  | .first => pop inputStack CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.getD false)
        (pop inputStack CarryProtocol.saveBit
          (push aStack (fun v => v.1.1.2.1.getD false)
            (load CarryProtocol.clearBit (goto (fun _ => .inr .first)))))
        (load CarryProtocol.clearBit (goto (fun _ => .inr .second))))
  | .second => pop inputStack CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push bStack (fun v => v.1.1.2.1.getD false)
          (load CarryProtocol.clearBit (goto (fun _ => .inr .second))))
        (load CarryProtocol.clearBit (goto (fun _ => .inr .inspect))))
  | .inspect => peek aStack (fun v bit => (v.1, (bit.getD false, v.2.2)))
      (peek bStack (fun v bit => (v.1, (v.2.1, bit.getD false)))
        (branch (fun v => v.2.1 == v.2.2)
          (load (fun v => ((BinaryArithmetic.Addition.reset v.2.1, ()), v.2))
            (goto (fun _ => .inl (.inl false))))
          (load (fun v => (BinaryArithmetic.Multiplication.clean, (false, v.2.1)))
            (goto (fun _ => .inr .columns)))))
  | .columns => columns
  | .clearF => NormalizeProtocol.clearStmt wStack (.inr .clearF) (fun _ => .inr .trimR)
  | .clearR => NormalizeProtocol.clearStmt rStack (.inr .clearR) (fun _ => .inr .trimF)
  | .trimF => NormalizeProtocol.trimStmt wStack outStack (.inr .trimF) (.inr .reverseF) (fun _ => .inr .finish)
  | .reverseF => CarryProtocol.restoreStmt outStack wStack (.inr .reverseF) (fun _ => .inr .finish)
  | .trimR => NormalizeProtocol.trimStmt rStack outStack (.inr .trimR) (.inr .reverseR) (fun _ => .inr .finish)
  | .reverseR => CarryProtocol.restoreStmt outStack rStack (.inr .reverseR) (fun _ => .inr .finish)
  | .finish => branch (fun v => v.2.1)
      (load (fun _ => initial) halt)
      (load CarryProtocol.clearBit (goto (fun _ => .inr .dec)))
  | .dec => CarryProtocol.decrementStmt outStack wStack (.inr .dec) (.inr .restoreDec)
  | .restoreDec => CarryProtocol.restoreStmt outStack wStack (.inr .restoreDec) (fun _ => .inr .halt)
  | .halt => load (fun _ => initial) halt

abbrev computer : FinTM2 where
  K := K
  k₀ := inputStack
  k₁ := outStack
  Γ _ := Bool
  Λ := Label
  main := .inr .first
  σ := Memory
  initialState := initial
  m := MachineReturn.program ret coreProgram outside
instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)
abbrev tapes := IntegerArithmetic.Multiplication.tapes

def cfg (label : Option Label) (signs : Signs) (a b w out r input : List Bool) : Config :=
  ⟨label, CarryProtocol.clean signs, tapes a b w out r [] input⟩
def pCfg (phase : Phase) (a b input : List Bool) : Config :=
  cfg (some (.inr phase)) (false, false) a b [] [] [] input
def colCfg (sign borrow reverseBorrow : Bool) (a b f r : List Bool) : Config :=
  ⟨some (.inr .columns), ((BinaryArithmetic.Addition.reset borrow, ()), (reverseBorrow, sign)), tapes a b f [] r [] []⟩
def addCfg (sign : Bool) (a b : List Bool) : Config :=
  ⟨some (.inl (.inl false)), ((BinaryArithmetic.Addition.reset sign, ()), (sign, sign)), tapes a b [] [] [] [] []⟩

@[simp] theorem tapes_output (a b w o m ds i : List Bool) : tapes a b w o m ds i outStack = o := rfl
@[simp] theorem update_output (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) outStack x = tapes a b w x m ds i := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, IntegerArithmetic.Multiplication.tapes, outStack,
        BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Addition.tapes]
    | inr k => cases k <;> simp [tapes, IntegerArithmetic.Multiplication.tapes, outStack,
        BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, IntegerArithmetic.Multiplication.tapes, outStack]

def Runs (start finish : Config) (n : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[n] (some start) = some finish
theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h
theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']
theorem executes (phase : Phase) : CarryProtocol.ExecutesAt computer.step (.inr phase) (outside phase) := by
  intro state tapes
  rfl


theorem step_first_cons (bit : Bool) (i a b : List Bool) :
    computer.step (pCfg .first a b (true :: bit :: i)) = some (pCfg .first (bit :: a) b i) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    aStack, inputStack, outStack]
  congr 2

theorem step_delimiter (i a b : List Bool) :
    computer.step (pCfg .first a b (false :: i)) = some (pCfg .second a b i) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    aStack, inputStack, outStack]
  congr 2

theorem step_second_cons (bit : Bool) (i a b : List Bool) :
    computer.step (pCfg .second a b (bit :: i)) = some (pCfg .second a (bit :: b) i) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    bStack, inputStack, outStack]
  congr 2

theorem step_second_nil (a b : List Bool) :
    computer.step (pCfg .second a b []) = some (pCfg .inspect a b []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    bStack, inputStack, outStack]
  congr 2

theorem step_columns_both (sa fb rb x y : Bool) (a b f r : List Bool) :
    computer.step (colCfg sa fb rb (x :: a) (y :: b) f r) = some (colCfg sa (digitBorrow fb x y) (digitBorrow rb y x) a b (digitDiff fb x y :: f) (digitDiff rb y x :: r)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    aStack, bStack, wStack, rStack, inputStack, outStack, colCfg, columns, BinaryArithmetic.Addition.reset]
  congr 2

theorem step_columns_left (sa fb rb x : Bool) (a f r : List Bool) :
    computer.step (colCfg sa fb rb (x :: a) [] f r) = some (colCfg sa (digitBorrow fb x false) (digitBorrow rb false x) a [] (digitDiff fb x false :: f) (digitDiff rb false x :: r)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    aStack, bStack, wStack, rStack, inputStack, outStack, colCfg, columns, BinaryArithmetic.Addition.reset]
  congr 2

theorem step_columns_right (sa fb rb y : Bool) (b f r : List Bool) :
    computer.step (colCfg sa fb rb [] (y :: b) f r) = some (colCfg sa (digitBorrow fb false y) (digitBorrow rb y false) [] b (digitDiff fb false y :: f) (digitDiff rb y false :: r)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    aStack, bStack, wStack, rStack, inputStack, outStack, colCfg, columns, BinaryArithmetic.Addition.reset]
  congr 2

theorem step_columns_done (sa fb rb : Bool) (f r : List Bool) :
    computer.step (colCfg sa fb rb [] [] f r) =
      some (cfg (some (.inr (if fb then .clearF else .clearR)))
        ((if fb then !sa else sa), false) [] [] f [] r []) := by
  cases fb <;> simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
    aStack, bStack, wStack, rStack, inputStack, outStack, colCfg, columns, BinaryArithmetic.Addition.reset] <;> congr 2

theorem first_exact (word i a b : List Bool) :
    Runs (pCfg .first a b (Holant.Algebraic.frame word ++ i))
      (pCfg .second (word.reverse ++ a) b i) (word.length + 1) := by
  induction word generalizing a with
  | nil => simpa [Holant.Algebraic.frame] using Runs.one (step_delimiter i a b)
  | cons bit word ih =>
    have h := (Runs.one (step_first_cons bit (Holant.Algebraic.frame word ++ i) a b)).trans (ih (bit :: a))
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

theorem second_exact (word a b : List Bool) :
    Runs (pCfg .second a b word) (pCfg .inspect a (word.reverse ++ b) []) (word.length + 1) := by
  induction word generalizing b with
  | nil => simpa using Runs.one (step_second_nil a b)
  | cons bit word ih =>
    have h := (Runs.one (step_second_cons bit word a b)).trans (ih (bit :: b))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem columns_exact (sa fb rb : Bool) (a b f r : List Bool) :
    Runs (colCfg sa fb rb a b f r)
      (cfg (some (.inr (if (subBits fb a b).2 then .clearF else .clearR)))
        ((if (subBits fb a b).2 then !sa else sa), false) [] []
        ((subBits fb a b).1.reverse ++ f) [] ((subBits rb b a).1.reverse ++ r) [])
      (max a.length b.length + 1) := by
  induction a generalizing b fb rb f r with
  | nil =>
    induction b generalizing fb rb f r with
    | nil => simpa [subBits] using Runs.one (step_columns_done sa fb rb f r)
    | cons y b ih =>
      have h := (Runs.one (step_columns_right sa fb rb y b f r)).trans
        (ih (digitBorrow fb false y) (digitBorrow rb y false) (digitDiff fb false y :: f) (digitDiff rb y false :: r))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
  | cons x a ih =>
    cases b with
    | nil =>
      have h := (Runs.one (step_columns_left sa fb rb x a f r)).trans
        (ih (digitBorrow fb x false) (digitBorrow rb false x) [] (digitDiff fb x false :: f) (digitDiff rb false x :: r))
      simpa [subBits, List.reverse_cons, List.append_assoc] using h
    | cons y b =>
      have h := (Runs.one (step_columns_both sa fb rb x y a b f r)).trans
        (ih (digitBorrow fb x y) (digitBorrow rb y x) b (digitDiff fb x y :: f) (digitDiff rb y x :: r))
      simpa [subBits, List.reverse_cons, List.append_assoc, Nat.succ_max_succ] using h


theorem step_inspect (a b : List Bool) :
    computer.step (pCfg .inspect a b []) =
      some (if a.head?.getD false = b.head?.getD false then addCfg (a.head?.getD false) a b
        else colCfg (a.head?.getD false) false false a b [] []) := by
  cases ha : a.head?.getD false <;> cases hb : b.head?.getD false <;>
    simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg, addCfg, colCfg,
      TM2.stepAux, CarryProtocol.clean, BinaryArithmetic.Multiplication.clean, BinaryArithmetic.Addition.initial,
      BinaryArithmetic.Addition.reset, aStack, bStack, ha, hb] <;> congr 2

theorem natural_exact (sign : Bool) (a b : List Bool) :
    Runs (addCfg sign a b)
      (cfg (some (.inr .halt)) (sign, sign) [] [] [] (addBits sign a b) [] [])
      (max a.length b.length + (addBits sign a b).length + 2) := by
  let start := BinaryArithmetic.Addition.cfg (some false) sign a b [] []
  let finish := BinaryArithmetic.Addition.cfg none false [] [] [] (addBits sign a b)
  have hs : (fun c => c.bind (TM2.step BinaryArithmetic.Addition.program))^[max a.length b.length + (addBits sign a b).length + 2]
      (some start) = some finish := BinaryArithmetic.Addition.compute_exact sign a b
  have hf := MachineFrame.run_program BinaryArithmetic.Addition.program coreOutside start () (fun _ : Bool => [])
    (max a.length b.length + (addBits sign a b).length + 2)
  rw [hs] at hf
  have h := MachineReturn.run_program ret coreProgram outside
    (MachineFrame.cfg start () (fun _ : Bool => [])) (sign, sign) (fun _ : Unit => [])
    (max a.length b.length + (addBits sign a b).length + 2)
    (MachineFrame.cfg finish () (fun _ : Bool => [])) hf
  have he : BinaryArithmetic.Multiplication.extras [] [] = (fun _ : Bool => []) := by
    funext k; cases k <;> rfl
  simpa only [Runs, FinTM2.step, computer, MachineReturn.cfg, MachineFrame.cfg, start, finish,
    BinaryArithmetic.Addition.cfg, BinaryArithmetic.Addition.reset, BinaryArithmetic.Addition.initial,
    CarryProtocol.clean, BinaryArithmetic.Multiplication.clean, addCfg, cfg, tapes,
    IntegerArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.tapes, ret,
    Option.map_some, Option.map_none, Option.elim_some, Option.elim_none, he] using h

theorem clearF_exact (neg : Bool) (f r : List Bool) :
    Runs (cfg (some (.inr .clearF)) (neg, false) [] [] f [] r [])
      (cfg (some (.inr .trimR)) (neg, false) [] [] [] [] r []) (f.length + 1) := by
  have h := NormalizeProtocol.clear_exact outStack wStack computer.step (.inr .clearF) (fun _ => .inr .trimR)
    (executes .clearF) (neg, false) (tapes [] [] f [] r [] []) f []
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_output,
    IntegerArithmetic.Multiplication.update_w, cfg, Runs, outStack, wStack] using h

theorem clearR_exact (neg : Bool) (f r : List Bool) :
    Runs (cfg (some (.inr .clearR)) (neg, false) [] [] f [] r [])
      (cfg (some (.inr .trimF)) (neg, false) [] [] f [] [] []) (r.length + 1) := by
  have h := NormalizeProtocol.clear_exact outStack rStack computer.step (.inr .clearR) (fun _ => .inr .trimF)
    (executes .clearR) (neg, false) (tapes [] [] f [] r [] []) r []
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_output,
    IntegerArithmetic.Multiplication.update_m, cfg, Runs, outStack, rStack] using h

theorem normalizeF_exact (neg : Bool) (word : List Bool) :
    Runs (cfg (some (.inr .trimF)) (neg, false) [] [] word [] [] [])
      (cfg (some (.inr .finish)) (neg, false) [] [] [] (normalize word.reverse) [] []) (word.length + 1) := by
  have h := NormalizeProtocol.normalize_exact outStack wStack (by decide) computer.step
    (.inr .trimF) (.inr .reverseF) (fun _ => .inr .finish) (executes .trimF) (executes .reverseF)
    (neg, false) (tapes [] [] word [] [] [] []) word
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_output,
    IntegerArithmetic.Multiplication.update_w, cfg, Runs, outStack, wStack] using h

theorem normalizeR_exact (neg : Bool) (word : List Bool) :
    Runs (cfg (some (.inr .trimR)) (neg, false) [] [] [] [] word [])
      (cfg (some (.inr .finish)) (neg, false) [] [] [] (normalize word.reverse) [] []) (word.length + 1) := by
  have h := NormalizeProtocol.normalize_exact outStack rStack (by decide) computer.step
    (.inr .trimR) (.inr .reverseR) (fun _ => .inr .finish) (executes .trimR) (executes .reverseR)
    (neg, false) (tapes [] [] [] [] word [] []) word
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_output,
    IntegerArithmetic.Multiplication.update_m, cfg, Runs, outStack, rStack] using h

theorem dec_exact (neg : Bool) (word : List Bool) :
    Runs (cfg (some (.inr .dec)) (neg, false) [] [] [] word [] [])
      (cfg (some (.inr .halt)) (neg, false) [] [] [] (decrement word) [] []) (2 * (borrowCount word + 1)) := by
  have h := CarryProtocol.decrement_exact_frame outStack wStack (by decide) computer.step
    (.inr .dec) (.inr .restoreDec) (fun _ => .inr .halt) (executes .dec) (executes .restoreDec)
    (neg, false) (tapes [] [] [] word [] [] []) word
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_output,
    IntegerArithmetic.Multiplication.update_w, cfg, Runs, outStack, wStack] using h

theorem step_halt (signs : Signs) (word : List Bool) :
    computer.step (cfg (some (.inr .halt)) signs [] [] [] word [] []) =
      some (cfg none (false, false) [] [] [] word [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, initial]
  congr 2

theorem step_finish_true (word : List Bool) :
    computer.step (cfg (some (.inr .finish)) (true, false) [] [] [] word [] []) =
      some (cfg none (false, false) [] [] [] word [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, initial, CarryProtocol.clean]
  congr 2

theorem step_finish_false (word : List Bool) :
    computer.step (cfg (some (.inr .finish)) (false, false) [] [] [] word [] []) =
      some (cfg (some (.inr .dec)) (false, false) [] [] [] word [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, cfg, TM2.stepAux, CarryProtocol.clearBit, CarryProtocol.clean]
  congr 2

def finishTime (neg : Bool) (word : List Bool) : ℕ := if neg then 1 else 2 * (borrowCount word + 1) + 2

theorem finish_exact (neg : Bool) (word : List Bool) :
    Runs (cfg (some (.inr .finish)) (neg, false) [] [] [] word [] [])
      (cfg none (false, false) [] [] [] (if neg then word else decrement word) [] []) (finishTime neg word) := by
  cases neg
  · have h := ((Runs.one (step_finish_false word)).trans (dec_exact false word)).trans
      (Runs.one (step_halt (false, false) (decrement word)))
    simp only [finishTime, Bool.false_eq_true, ↓reduceIte]
    convert h using 1
    omega
  · exact Runs.one (step_finish_true word)

theorem finishTime_le (neg : Bool) (word : List Bool) : finishTime neg word ≤ 2 * word.length + 4 := by
  have h := borrowCount_le word
  cases neg <;> simp [finishTime]
  omega


def selectedSign (sign borrow : Bool) : Bool := if borrow then !sign else sign
def selectedWord (borrow : Bool) (f r : List Bool) : List Bool := if borrow then normalize r else normalize f

theorem after_columns_exact (sign borrow : Bool) (f r : List Bool) :
    Runs (cfg (some (.inr (if borrow then .clearF else .clearR))) (selectedSign sign borrow, false)
        [] [] f.reverse [] r.reverse [])
      (cfg none (false, false) [] [] []
        (if selectedSign sign borrow then selectedWord borrow f r else decrement (selectedWord borrow f r)) [] [])
      (f.length + r.length + 2 + finishTime (selectedSign sign borrow) (selectedWord borrow f r)) := by
  cases borrow
  · have hc := clearR_exact sign f.reverse r.reverse
    have hn := normalizeF_exact sign f.reverse
    simp only [List.reverse_reverse] at hn
    have h := (hc.trans hn).trans (finish_exact sign (normalize f))
    simp only [selectedSign, selectedWord, Bool.false_eq_true, ↓reduceIte]
    convert h using 1
    simp only [List.length_reverse]
    omega
  · have hc := clearF_exact (!sign) f.reverse r.reverse
    have hn := normalizeR_exact (!sign) r.reverse
    simp only [List.reverse_reverse] at hn
    have h := (hc.trans hn).trans (finish_exact (!sign) (normalize r))
    simp only [selectedSign, selectedWord, ↓reduceIte]
    convert h using 1
    simp only [List.length_reverse]
    omega

def mixedTime (sign : Bool) (a b : List Bool) : ℕ :=
  3 * max a.length b.length + 3 +
    finishTime (selectedSign sign (subBits false a b).2)
      (selectedWord (subBits false a b).2 (subBits false a b).1 (subBits false b a).1)

theorem mixed_exact (sign : Bool) (a b : List Bool) :
    Runs (colCfg sign false false a b [] [])
      (cfg none (false, false) [] [] [] (mixedBits sign a b) [] []) (mixedTime sign a b) := by
  have hc := columns_exact sign false false a b [] []
  simp only [List.append_nil] at hc
  have h := hc.trans (after_columns_exact sign (subBits false a b).2
    (subBits false a b).1 (subBits false b a).1)
  have hw : (if selectedSign sign (subBits false a b).2 then
      selectedWord (subBits false a b).2 (subBits false a b).1 (subBits false b a).1
    else decrement (selectedWord (subBits false a b).2 (subBits false a b).1 (subBits false b a).1)) =
      mixedBits sign a b := by
    cases sign <;> cases hb : (subBits false a b).2 <;> simp [mixedBits, selectedSign, selectedWord, hb]
  rw [hw] at h
  convert h using 1
  simp only [mixedTime, subBits_length, Nat.max_comm b.length a.length]
  omega

theorem selectedWord_length_le (a b : List Bool) :
    (selectedWord (subBits false a b).2 (subBits false a b).1 (subBits false b a).1).length ≤ max a.length b.length := by
  have hf := normalize_length_le (subBits false a b).1
  have hr := normalize_length_le (subBits false b a).1
  rw [subBits_length] at hf hr
  unfold selectedWord
  split <;> omega

theorem mixedTime_le (sign : Bool) (a b : List Bool) : mixedTime sign a b ≤ 5 * max a.length b.length + 7 := by
  have hl := selectedWord_length_le a b
  have ht := finishTime_le (selectedSign sign (subBits false a b).2)
    (selectedWord (subBits false a b).2 (subBits false a b).1 (subBits false b a).1)
  unfold mixedTime
  omega

def operationTime (sa sb : Bool) (a b : List Bool) : ℕ :=
  if sa = sb then max a.length b.length + (addBits sa a b).length + 3 else mixedTime sa a b

theorem operationTime_le (sa sb : Bool) (a b : List Bool) :
    operationTime sa sb a b ≤ 5 * max a.length b.length + 7 := by
  have hm := mixedTime_le sa a b
  have ha := addBits_length_le sa a b
  unfold operationTime
  split <;> omega

theorem operation_exact (sa sb : Bool) (a b : List Bool)
    (ha : a.head?.getD false = sa) (hb : b.head?.getD false = sb) :
    Runs (pCfg .inspect a b [])
      (cfg none (false, false) [] [] [] (sumBits sa sb a b) [] []) (1 + operationTime sa sb a b) := by
  have hi := Runs.one (step_inspect a b)
  rw [ha, hb] at hi
  by_cases hs : sa = sb
  · cases hs
    simp only [↓reduceIte] at hi
    have h := (hi.trans (natural_exact sa a b)).trans
      (Runs.one (step_halt (sa, sa) (addBits sa a b)))
    simp only [sumBits, operationTime, ↓reduceIte]
    convert h using 1
  · simp only [hs, ↓reduceIte] at hi
    have h := hi.trans (mixed_exact sa a b)
    simpa only [sumBits, operationTime, hs, ↓reduceIte, Nat.add_comm] using h

def time (a b : ℤ) : ℕ := (encoding.encode a).length + (encoding.encode b).length + 3 +
  operationTime (negative a) (negative b) (encoding.encode a) (encoding.encode b)

theorem cfg_init (input : List Bool) : pCfg .first [] [] input = initList computer input := by
  dsimp [pCfg, cfg, initList, computer, initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

theorem cfg_halt (word : List Bool) :
    cfg none (false, false) [] [] [] word [] [] = haltList computer word := by
  dsimp [cfg, haltList, computer, initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

/-- Canonical signed addition, with every parsing, arithmetic and cleanup step counted. -/
theorem encoded_exact (a b : ℤ) :
    Runs (initList computer (pairEncoding.encode (a, b)))
      (haltList computer (encoding.encode (a + b))) (time a b) := by
  have h₁ := first_exact (encoding.encode a).reverse (encoding.encode b).reverse [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact (encoding.encode b).reverse (encoding.encode a) []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := operation_exact (negative a) (negative b) (encoding.encode a) (encoding.encode b)
    (encoding_head a) (encoding_head b)
  rw [sumBits_encoding] at h₃
  have h := (h₁.trans h₂).trans h₃
  rw [cfg_init, cfg_halt] at h
  change Runs (initList computer (pairEncoding.encode (a, b))) _ _ at h
  convert h using 1
  simp only [time, List.length_reverse]
  omega

theorem time_le (a b : ℤ) : time a b ≤ 6 * (pairEncoding.encode (a, b)).length + 10 := by
  have h := operationTime_le (negative a) (negative b) (encoding.encode a) (encoding.encode b)
  simp only [time, pairEncoding_length]
  omega

/-- A linear-time finite binary machine for signed addition in the established codec. -/
noncomputable def additionPolyTime : PolyTime pairEncoding encoding (fun p => p.1 + p.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 10
  outputsFun p := by
    change TM2OutputsInTime computer (List.map id (pairEncoding.encode p))
      (some (List.map id (encoding.encode (p.1 + p.2))))
      ((6 * Polynomial.X + 10).eval (pairEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := time p.1 p.2
             evals_in_steps := encoded_exact p.1 p.2
             steps_le_m := ?_ }
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Prod.eta]
      using time_le p.1 p.2
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem addition_inFP : InFP pairEncoding encoding (fun p => p.1 + p.2) := ⟨additionPolyTime⟩

theorem outside_budget (phase : Phase) : TM2Cost.budget (outside phase) ≤ 8 := by
  cases phase <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 8 := by
  cases label with
  | inl label =>
    cases label with
    | inl label =>
      simp only [computer, MachineReturn.program, MachineReturn.budget_stmt, coreProgram,
        MachineFrame.program, MachineFrame.budget_stmt]
      exact le_trans (BinaryArithmetic.Addition.program_budget label) (by decide)
    | inr e => exact nomatch e
  | inr phase => exact outside_budget phase

@[simp] theorem stack_count : Fintype.card computer.K = 7 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 16 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 72 := by decide

end Holant.Complexity.IntegerArithmetic.Addition

end Holant.LocalDrafts.RemoteWork.CountingBridge.AnswerDecoder.Port
