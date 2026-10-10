import Holant.Complexity.IntegerArithmetic.CarryProtocol

/-!
# Finite signed multiplication in the established integer codec

The parser reads both parity codes, preserves two sign bits, and uses actual
carry loops to increment negative-successor payloads. It then invokes the
verified natural multiplier. A final actual borrow loop reconstructs a negative
parity code; zero always uses the empty, positive encoding.
-/

namespace Holant.Complexity.IntegerArithmetic.Multiplication

open Turing Computability BinaryArithmetic
open Turing.TM2.Stmt

abbrev NatMul := BinaryArithmetic.Multiplication.computer
abbrev NK := BinaryArithmetic.Multiplication.K
abbrev NL := BinaryArithmetic.Multiplication.Label
abbrev Signs := CarryProtocol.Signs
abbrev Memory := CarryProtocol.Memory

inductive Phase
  | first | second | signs | incA | restoreA | incB | restoreB | reverse
  | finish | dec | restoreDec | tag
  deriving DecidableEq
instance : Fintype Phase := ⟨{.first, .second, .signs, .incA, .restoreA, .incB, .restoreB,
  .reverse, .finish, .dec, .restoreDec, .tag}, by intro p; cases p <;> simp⟩

abbrev K := NK ⊕ Unit
abbrev Label := NL ⊕ Phase
abbrev Config := TM2.Cfg (fun _ : K => Bool) Label Memory
abbrev Statement := TM2.Stmt (fun _ : K => Bool) Label Memory

abbrev inputStack : K := .inr ()
abbrev mStack : K := .inl (.inr false)
abbrev bStack : K := .inl (.inl .right)
abbrev wStack : K := .inl (.inl .work)
abbrev nStack : K := .inl (.inr true)
abbrev outStack : K := .inl (.inl .left)

def initial : Memory := CarryProtocol.clean (false, false)
def ret (_ : Signs) : Phase := .finish
def choose (signs : Signs) : Label := .inr (if signs.1 then .incA else if signs.2 then .incB else .reverse)
def afterA (signs : Signs) : Label := .inr (if signs.2 then .incB else .reverse)

def outside : Phase → Statement
  | .first => pop inputStack CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.getD false)
        (pop inputStack CarryProtocol.saveBit
          (push mStack (fun v => v.1.1.2.1.getD false)
            (load CarryProtocol.clearBit (goto (fun _ => .inr .first)))))
        (load CarryProtocol.clearBit (goto (fun _ => .inr .second))))
  | .second => pop inputStack CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push bStack (fun v => v.1.1.2.1.getD false)
          (load CarryProtocol.clearBit (goto (fun _ => .inr .second))))
        (load CarryProtocol.clearBit (goto (fun _ => .inr .signs))))
  | .signs => pop mStack (fun v bit => (v.1, (bit.getD false, v.2.2)))
      (pop bStack (fun v bit => (v.1, (v.2.1, bit.getD false)))
        (goto (fun v => choose v.2)))
  | .incA => CarryProtocol.incrementStmt mStack wStack (.inr .incA) (.inr .restoreA)
  | .restoreA => CarryProtocol.restoreStmt mStack wStack (.inr .restoreA) afterA
  | .incB => CarryProtocol.incrementStmt bStack wStack (.inr .incB) (.inr .restoreB)
  | .restoreB => CarryProtocol.restoreStmt bStack wStack (.inr .restoreB) (fun _ => .inr .reverse)
  | .reverse => pop bStack CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (push nStack (fun v => v.1.1.2.1.getD false)
          (load CarryProtocol.clearBit (goto (fun _ => .inr .reverse))))
        (load CarryProtocol.clearBit (goto (fun _ => .inl (.inr .loop)))))
  | .finish => peek outStack CarryProtocol.saveBit
      (branch (fun v => v.1.1.2.1.isSome)
        (branch (fun v => xor v.2.1 v.2.2)
          (load CarryProtocol.clearBit (goto (fun _ => .inr .dec)))
          (push outStack (fun _ => false) (load (fun _ => initial) halt)))
        (load (fun _ => initial) halt))
  | .dec => CarryProtocol.decrementStmt outStack wStack (.inr .dec) (.inr .restoreDec)
  | .restoreDec => CarryProtocol.restoreStmt outStack wStack (.inr .restoreDec) (fun _ => .inr .tag)
  | .tag => push outStack (fun _ => true) (load (fun _ => initial) halt)

abbrev computer : FinTM2 where
  K := K
  k₀ := inputStack
  k₁ := outStack
  Γ _ := Bool
  Λ := Label
  main := .inr .first
  σ := Memory
  initialState := initial
  m := MachineReturn.program ret NatMul.m outside

instance finiteAlphabet (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def tapes (a b w o m digits input : List Bool) : K → List Bool :=
  Sum.elim (BinaryArithmetic.Multiplication.tapes a b w o m digits) (fun _ => input)

def cfg (label : Option Label) (signs : Signs) (a b w o m digits input : List Bool) : Config :=
  ⟨label, CarryProtocol.clean signs, tapes a b w o m digits input⟩

def pCfg (phase : Phase) (signs : Signs) (input m b w digits : List Bool) : Config :=
  cfg (some (.inr phase)) signs [] b w [] m digits input

def dCfg (phase : Phase) (signs : Signs) (word work : List Bool) : Config :=
  cfg (some (.inr phase)) signs word [] work [] [] [] []

@[simp] theorem tapes_m (a b w o m ds i : List Bool) : tapes a b w o m ds i mStack = m := rfl
@[simp] theorem tapes_b (a b w o m ds i : List Bool) : tapes a b w o m ds i bStack = b := rfl
@[simp] theorem tapes_w (a b w o m ds i : List Bool) : tapes a b w o m ds i wStack = w := rfl
@[simp] theorem tapes_n (a b w o m ds i : List Bool) : tapes a b w o m ds i nStack = ds := rfl
@[simp] theorem tapes_out (a b w o m ds i : List Bool) : tapes a b w o m ds i outStack = a := rfl
@[simp] theorem tapes_input (a b w o m ds i : List Bool) : tapes a b w o m ds i inputStack = i := rfl

@[simp] theorem update_m (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) mStack x = tapes a b w o x ds i := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, mStack, BinaryArithmetic.Multiplication.tapes, Addition.tapes]
    | inr k => cases k <;> simp [tapes, mStack, BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, mStack]

@[simp] theorem update_b (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) bStack x = tapes a x w o m ds i := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, bStack, BinaryArithmetic.Multiplication.tapes, Addition.tapes]
    | inr k => cases k <;> simp [tapes, bStack, BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, bStack]

@[simp] theorem update_w (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) wStack x = tapes a b x o m ds i := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, wStack, BinaryArithmetic.Multiplication.tapes, Addition.tapes]
    | inr k => cases k <;> simp [tapes, wStack, BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, wStack]

@[simp] theorem update_n (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) nStack x = tapes a b w o m x i := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, nStack, BinaryArithmetic.Multiplication.tapes, Addition.tapes]
    | inr k => cases k <;> simp [tapes, nStack, BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, nStack]

@[simp] theorem update_out (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) outStack x = tapes x b w o m ds i := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, outStack, BinaryArithmetic.Multiplication.tapes, Addition.tapes]
    | inr k => cases k <;> simp [tapes, outStack, BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, outStack]

@[simp] theorem update_input (a b w o m ds i x : List Bool) :
    Function.update (tapes a b w o m ds i) inputStack x = tapes a b w o m ds x := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> simp [tapes, inputStack, BinaryArithmetic.Multiplication.tapes, Addition.tapes]
    | inr k => cases k <;> simp [tapes, inputStack, BinaryArithmetic.Multiplication.tapes, BinaryArithmetic.Multiplication.extras]
  | inr k => cases k; simp [tapes, inputStack]

def Runs (start finish : Config) (time : ℕ) : Prop :=
  (fun c => c.bind computer.step)^[time] (some start) = some finish

theorem Runs.one {a b : Config} (h : computer.step a = some b) : Runs a b 1 := h

theorem Runs.trans {a b c : Config} {n m : ℕ} (h : Runs a b n) (h' : Runs b c m) :
    Runs a c (m + n) := by
  unfold Runs at *
  rw [Function.iterate_add_apply, h, h']

theorem executes (phase : Phase) : CarryProtocol.ExecutesAt computer.step (.inr phase) (outside phase) := by
  intro state tapes
  rfl

theorem step_first_cons (bit : Bool) (i m b : List Bool) :
    computer.step (pCfg .first (false, false) (true :: bit :: i) m b [] []) = some (pCfg .first (false, false) i (bit :: m) b [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_delimiter (i m b : List Bool) :
    computer.step (pCfg .first (false, false) (false :: i) m b [] []) = some (pCfg .second (false, false) i m b [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_second_cons (bit : Bool) (i m b : List Bool) :
    computer.step (pCfg .second (false, false) (bit :: i) m b [] []) = some (pCfg .second (false, false) i m (bit :: b) [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_second_nil (m b : List Bool) :
    computer.step (pCfg .second (false, false) [] m b [] []) = some (pCfg .signs (false, false) [] m b [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_reverse_cons (signs : Signs) (bit : Bool) (m b ds : List Bool) :
    computer.step (pCfg .reverse signs [] m (bit :: b) [] ds) = some (pCfg .reverse signs [] m b [] (bit :: ds)) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_reverse_nil (signs : Signs) (m ds : List Bool) :
    computer.step (pCfg .reverse signs [] m [] [] ds) = some (cfg (some (.inl (.inr .loop))) signs [] [] [] [] m ds []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_signs (a b : List Bool) :
    computer.step (pCfg .signs (false, false) [] a b [] []) =
      some (cfg (some (choose (a.head?.getD false, b.head?.getD false)))
        (a.head?.getD false, b.head?.getD false) [] b.tail [] [] a.tail [] []) := by
  cases a <;> cases b <;>
    simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, pCfg, cfg,
      TM2.stepAux, CarryProtocol.clean] <;> congr 2

theorem first_exact (word i m b : List Bool) :
    Runs (pCfg .first (false, false) (Holant.Algebraic.frame word ++ i) m b [] [])
      (pCfg .second (false, false) i (word.reverse ++ m) b [] []) (word.length + 1) := by
  induction word generalizing m with
  | nil => simpa [Holant.Algebraic.frame] using Runs.one (step_delimiter i m b)
  | cons bit word ih =>
    have h := (Runs.one (step_first_cons bit (Holant.Algebraic.frame word ++ i) m b)).trans (ih (bit :: m))
    simpa [Holant.Algebraic.frame, List.reverse_cons, List.append_assoc] using h

theorem second_exact (word m b : List Bool) :
    Runs (pCfg .second (false, false) word m b [] [])
      (pCfg .signs (false, false) [] m (word.reverse ++ b) [] []) (word.length + 1) := by
  induction word generalizing b with
  | nil => simpa using Runs.one (step_second_nil m b)
  | cons bit word ih =>
    have h := (Runs.one (step_second_cons bit word m b)).trans (ih (bit :: b))
    simpa [List.reverse_cons, List.append_assoc] using h

theorem reverse_exact (signs : Signs) (word m ds : List Bool) :
    Runs (pCfg .reverse signs [] m word [] ds)
      (cfg (some (.inl (.inr .loop))) signs [] [] [] [] m (word.reverse ++ ds) []) (word.length + 1) := by
  induction word generalizing ds with
  | nil => simpa using Runs.one (step_reverse_nil signs m ds)
  | cons bit word ih =>
    have h := (Runs.one (step_reverse_cons signs bit m word ds)).trans (ih (bit :: ds))
    simpa [List.reverse_cons, List.append_assoc] using h


theorem incA_exact (signs : Signs) (a b : List Bool) :
    Runs (pCfg .incA signs [] a b [] [])
      (cfg (some (afterA signs)) signs [] b [] [] (increment a) [] []) (2 * (carryCount a + 1)) := by
  have h := CarryProtocol.increment_exact_frame mStack wStack (by decide) computer.step
    (.inr .incA) (.inr .restoreA) afterA (executes .incA) (executes .restoreA)
    signs (tapes [] b [] [] a [] []) a
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_m, update_w, pCfg, cfg, Runs] using h

theorem incB_exact (signs : Signs) (a b : List Bool) :
    Runs (pCfg .incB signs [] a b [] [])
      (pCfg .reverse signs [] a (increment b) [] []) (2 * (carryCount b + 1)) := by
  have h := CarryProtocol.increment_exact_frame bStack wStack (by decide) computer.step
    (.inr .incB) (.inr .restoreB) (fun _ => .inr .reverse) (executes .incB) (executes .restoreB)
    signs (tapes [] b [] [] a [] []) b
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_b, update_w, pCfg, cfg, Runs] using h

theorem dec_exact (signs : Signs) (word : List Bool) :
    Runs (dCfg .dec signs word []) (dCfg .tag signs (decrement word) []) (2 * (borrowCount word + 1)) := by
  have h := CarryProtocol.decrement_exact_frame outStack wStack (by decide) computer.step
    (.inr .dec) (.inr .restoreDec) (fun _ => .inr .tag) (executes .dec) (executes .restoreDec)
    signs (tapes word [] [] [] [] [] []) word
  simpa only [CarryProtocol.Runs, CarryProtocol.cfg, CarryProtocol.tapes2, update_out, update_w, dCfg, cfg, Runs] using h

def incrementIf (sign : Bool) (word : List Bool) : List Bool := if sign then increment word else word

def prepareTime (signs : Signs) (a b : List Bool) : ℕ :=
  (if signs.1 then 2 * (carryCount a + 1) else 0) + (if signs.2 then 2 * (carryCount b + 1) else 0)

theorem prepare_exact (signs : Signs) (a b : List Bool) :
    Runs (cfg (some (choose signs)) signs [] b [] [] a [] [])
      (pCfg .reverse signs [] (incrementIf signs.1 a) (incrementIf signs.2 b) [] [])
      (prepareTime signs a b) := by
  rcases signs with ⟨sa, sb⟩
  cases sa <;> cases sb
  · rfl
  · simpa [choose, incrementIf, prepareTime, pCfg] using incB_exact (false, true) a b
  · simpa [choose, afterA, incrementIf, prepareTime, pCfg] using incA_exact (true, false) a b
  · have ha := incA_exact (true, true) a b
    have h := ha.trans (incB_exact (true, true) (increment a) b)
    simpa [choose, afterA, incrementIf, prepareTime, pCfg, Nat.add_comm] using h

theorem prepareTime_le (signs : Signs) (a b : List Bool) :
    prepareTime signs a b ≤ 2 * (a.length + b.length) + 4 := by
  have ha := carryCount_le a
  have hb := carryCount_le b
  rcases signs with ⟨sa, sb⟩
  cases sa <;> cases sb <;> simp [prepareTime] <;> omega

theorem magnitude_exact (a b : ℤ) :
    Runs (pCfg .signs (false, false) [] (encoding.encode a) (encoding.encode b) [] [])
      (cfg (some (.inl (.inr .loop))) (negative a, negative b) [] [] [] []
        (encodeNat a.natAbs) (encodeNat b.natAbs).reverse [])
      (1 + prepareTime (negative a, negative b) (encoding.encode a).tail (encoding.encode b).tail +
        (encodeNat b.natAbs).length + 1) := by
  have hs := Runs.one (step_signs (encoding.encode a) (encoding.encode b))
  simp only [encoding_head] at hs
  have hp := prepare_exact (negative a, negative b) (encoding.encode a).tail (encoding.encode b).tail
  change Runs _ (pCfg .reverse (negative a, negative b) [] (magnitudeBits a) (magnitudeBits b) [] []) _ at hp
  rw [magnitudeBits_eq, magnitudeBits_eq] at hp
  have hr := reverse_exact (negative a, negative b) (encodeNat b.natAbs) (encodeNat a.natAbs) []
  simp only [List.append_nil] at hr
  have h := (hs.trans hp).trans hr
  convert h using 1
  omega

theorem natural_exact (signs : Signs) (a b : ℕ) :
    Runs (cfg (some (.inl (.inr .loop))) signs [] [] [] [] (encodeNat a) (encodeNat b).reverse [])
      (dCfg .finish signs (encodeNat (a * b)) [])
      (MultiplyBits.time (encodeNat a) (encodeNat b).reverse []) := by
  have h := MachineReturn.run_program ret NatMul.m outside
    (BinaryArithmetic.Multiplication.cfg (some (.inr .loop)) [] [] [] [] (encodeNat a) (encodeNat b).reverse)
    signs (fun _ : Unit => []) (MultiplyBits.time (encodeNat a) (encodeNat b).reverse [])
    (BinaryArithmetic.Multiplication.cfg none (encodeNat (a * b)) [] [] [] [] [])
    (BinaryArithmetic.Multiplication.compute_encodeNat_exact a b)
  simpa only [Runs, FinTM2.step, computer, MachineReturn.cfg, BinaryArithmetic.Multiplication.cfg,
    cfg, dCfg, CarryProtocol.clean, tapes, ret, Option.elim_some, Option.elim_none] using h

theorem step_finish_nil (signs : Signs) :
    computer.step (dCfg .finish signs [] []) = some (cfg none (false, false) [] [] [] [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, dCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean, initial,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial]
  congr 2

theorem step_finish_pos (signs : Signs) (bit : Bool) (word : List Bool) (hs : xor signs.1 signs.2 = false) :
    computer.step (dCfg .finish signs (bit :: word) []) =
      some (cfg none (false, false) (false :: bit :: word) [] [] [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, dCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean, initial,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial, hs]
  congr 2

theorem step_finish_neg (signs : Signs) (bit : Bool) (word : List Bool) (hs : xor signs.1 signs.2 = true) :
    computer.step (dCfg .finish signs (bit :: word) []) = some (dCfg .dec signs (bit :: word) []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, dCfg, cfg,
    TM2.stepAux, CarryProtocol.saveBit, CarryProtocol.clearBit, CarryProtocol.clean, initial,
    BinaryArithmetic.Multiplication.saveBit, BinaryArithmetic.Multiplication.clean, Addition.initial, hs]
  congr 2

theorem step_tag (signs : Signs) (word : List Bool) :
    computer.step (dCfg .tag signs word []) =
      some (cfg none (false, false) (true :: word) [] [] [] [] [] []) := by
  simp [FinTM2.step, TM2.step, computer, MachineReturn.program, outside, dCfg, cfg,
    TM2.stepAux, CarryProtocol.clean, initial]
  congr 2

def recodeTime (sign : Bool) (word : List Bool) : ℕ :=
  if word = [] then 1 else if sign then 2 * (borrowCount word + 1) + 2 else 1

theorem recode_exact (signs : Signs) (word : List Bool) :
    Runs (dCfg .finish signs word [])
      (cfg none (false, false) (recode (xor signs.1 signs.2) word) [] [] [] [] [] [])
      (recodeTime (xor signs.1 signs.2) word) := by
  cases word with
  | nil => simpa [recode, recodeTime] using Runs.one (step_finish_nil signs)
  | cons bit word =>
    cases hs : xor signs.1 signs.2 with
    | false => simpa [recode, recodeTime, hs] using Runs.one (step_finish_pos signs bit word hs)
    | true =>
      have h := ((Runs.one (step_finish_neg signs bit word hs)).trans (dec_exact signs (bit :: word))).trans
        (Runs.one (step_tag signs (decrement (bit :: word))))
      simp only [recode, recodeTime, List.cons_ne_nil, ↓reduceIte]
      convert h using 1
      omega

theorem recodeTime_le (sign : Bool) (word : List Bool) : recodeTime sign word ≤ 2 * word.length + 4 := by
  have h := borrowCount_le word
  unfold recodeTime
  split <;> (try split) <;> omega

def time (a b : ℤ) : ℕ :=
  (encoding.encode a).length + (encoding.encode b).length + (encodeNat b.natAbs).length + 4 +
    prepareTime (negative a, negative b) (encoding.encode a).tail (encoding.encode b).tail +
    MultiplyBits.time (encodeNat a.natAbs) (encodeNat b.natAbs).reverse [] +
    recodeTime (xor (negative a) (negative b)) (encodeNat (a.natAbs * b.natAbs))

theorem cfg_init (input : List Bool) : pCfg .first (false, false) input [] [] [] [] = initList computer input := by
  dsimp [pCfg, cfg, initList, computer, initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

theorem cfg_halt (word : List Bool) :
    cfg none (false, false) word [] [] [] [] [] [] = haltList computer word := by
  dsimp [cfg, haltList, computer, initial]
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k; rfl

/-- Exact signed execution using only finite binary-stack syntax. -/
theorem encoded_exact (a b : ℤ) :
    Runs (initList computer (pairEncoding.encode (a, b)))
      (haltList computer (encoding.encode (a * b))) (time a b) := by
  have h₁ := first_exact (encoding.encode a).reverse (encoding.encode b).reverse [] []
  simp only [List.reverse_reverse, List.append_nil] at h₁
  have h₂ := second_exact (encoding.encode b).reverse (encoding.encode a) []
  simp only [List.reverse_reverse, List.append_nil] at h₂
  have h₃ := magnitude_exact a b
  have h₄ := natural_exact (negative a, negative b) a.natAbs b.natAbs
  have h₅ := recode_exact (negative a, negative b) (encodeNat (a.natAbs * b.natAbs))
  simp only [recode_encodeNat, signed_mul] at h₅
  have h := (((h₁.trans h₂).trans h₃).trans h₄).trans h₅
  rw [cfg_halt, cfg_init] at h
  change Runs (initList computer (pairEncoding.encode (a, b))) _ _ at h
  convert h using 1
  simp only [time, List.length_reverse]
  omega

/-- The exact transition count is bounded by a concrete cubic input-length polynomial. -/
theorem time_le (a b : ℤ) :
    time a b ≤
      ((pairEncoding.encode (a, b)).length + 2) *
        (6 * (((pairEncoding.encode (a, b)).length + 2) * ((pairEncoding.encode (a, b)).length + 3) + 3)) +
      2 * (((pairEncoding.encode (a, b)).length + 1) * ((pairEncoding.encode (a, b)).length + 3)) +
      4 * (pairEncoding.encode (a, b)).length + 13 := by
  let L := (pairEncoding.encode (a, b)).length
  have hab : (encoding.encode a).length + (encoding.encode b).length ≤ L := by
    dsimp [L]; simp only [pairEncoding_length]; omega
  have hma := magnitudeBits_length_le a
  have hmb := magnitudeBits_length_le b
  have ha : (encodeNat a.natAbs).length ≤ L + 1 := by omega
  have hb : (encodeNat b.natAbs).length ≤ L + 1 := by omega
  have hta : (encoding.encode a).tail.length ≤ (encoding.encode a).length := by simp
  have htb : (encoding.encode b).tail.length ≤ (encoding.encode b).length := by simp
  have hp₀ := prepareTime_le (negative a, negative b) (encoding.encode a).tail (encoding.encode b).tail
  have hp : prepareTime (negative a, negative b) (encoding.encode a).tail (encoding.encode b).tail ≤ 2 * L + 4 := by omega
  have hm₀ := MultiplyBits.time_le (encodeNat a.natAbs) (encodeNat b.natAbs).reverse []
  simp only [List.length_reverse, List.length_nil, Nat.zero_add] at hm₀
  have hprod : ((encodeNat b.natAbs).length + 1) * ((encodeNat a.natAbs).length + 2) ≤
      (L + 2) * (L + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hm : MultiplyBits.time (encodeNat a.natAbs) (encodeNat b.natAbs).reverse [] ≤
      (L + 2) * (6 * ((L + 2) * (L + 3) + 3)) :=
    le_trans hm₀ (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 6 (Nat.add_le_add_right hprod 3)))
  have ho₀ := product_length_le a.natAbs b.natAbs
  have ho : (encodeNat (a.natAbs * b.natAbs)).length ≤ (L + 1) * (L + 3) :=
    le_trans ho₀ (Nat.mul_le_mul hb (by omega))
  have hr₀ := recodeTime_le (xor (negative a) (negative b)) (encodeNat (a.natAbs * b.natAbs))
  unfold time
  change _ ≤ (L + 2) * (6 * ((L + 2) * (L + 3) + 3)) + 2 * ((L + 1) * (L + 3)) + 4 * L + 13
  omega

/-- Genuine finite-machine polynomial time for signed multiplication in the
same integer convention that the established rational code packs with `Nat.pair`. -/
noncomputable def multiplicationPolyTime : PolyTime pairEncoding encoding (fun p => p.1 * p.2) where
  tm := computer
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := (Polynomial.X + 2) * (6 * ((Polynomial.X + 2) * (Polynomial.X + 3) + 3)) +
    2 * ((Polynomial.X + 1) * (Polynomial.X + 3)) + 4 * Polynomial.X + 13
  outputsFun p := by
    change TM2OutputsInTime computer (List.map id (pairEncoding.encode p))
      (some (List.map id (encoding.encode (p.1 * p.2))))
      (((Polynomial.X + 2) * (6 * ((Polynomial.X + 2) * (Polynomial.X + 3) + 3)) +
        2 * ((Polynomial.X + 1) * (Polynomial.X + 3)) + 4 * Polynomial.X + 13).eval (pairEncoding.encode p).length)
    rw [List.map_id, List.map_id]
    refine { steps := time p.1 p.2
             evals_in_steps := encoded_exact p.1 p.2
             steps_le_m := ?_ }
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one, Prod.eta] using time_le p.1 p.2
  finiteAlphabets _ := inferInstanceAs (Fintype Bool)

theorem multiplication_inFP : InFP pairEncoding encoding (fun p => p.1 * p.2) := ⟨multiplicationPolyTime⟩

theorem outside_budget (phase : Phase) : TM2Cost.budget (outside phase) ≤ 8 := by
  cases phase <;> decide

theorem program_budget (label : Label) : TM2Cost.budget (computer.m label) ≤ 8 := by
  cases label with
  | inl label =>
    simpa only [computer, MachineReturn.program, MachineReturn.budget_stmt] using BinaryArithmetic.Multiplication.program_budget label
  | inr phase => exact outside_budget phase

@[simp] theorem stack_count : Fintype.card computer.K = 7 := by decide
@[simp] theorem label_count : Fintype.card computer.Λ = 20 := by decide
@[simp] theorem state_count : Fintype.card computer.σ = 72 := by decide

end Holant.Complexity.IntegerArithmetic.Multiplication
