import Holant.OneHot.StackProgram.Machine.StackWord
import Holant.OneHot.StackProgram.Machine.Constants
import Mathlib.Tactic.Linarith

/-!
# Finite bit-stack microprograms for bounded stack rearrangement

Nine fixed raw-word buffers and one reversal scratch stack suffice for every
Fin8 copy/erase and swap. Microinstructions are implemented by the already
proved literal bit loops; semantic word operations appear only in specifications.
-/
namespace Holant.OneHot.StackProgram.Machine.Rearrange
open Turing Computability Holant.Complexity StackProtocol

inductive Key where
  | data
  | buffer (i : Fin 9)
  | scratch
  deriving DecidableEq, Fintype

inductive Micro where
  | pop (i : Fin 9)
  | push (i : Fin 9)
  | copy (i j : Fin 9)
  | clear (i : Fin 9)
  deriving DecidableEq, Repr

@[ext] structure Data where
  stack : List (List Bool)
  buffers : Fin 9 → List Bool

/-- Identity word encoding, with actual list framing added by the stack codec. -/
def wordEncoding : Encoding (List Bool) Bool where
  encode := id
  decode := some
  decode_encode _ := rfl

def tapes (d : Data) : Key → List Bool
  | .data => (stackEncoding wordEncoding).encode d.stack
  | .buffer i => d.buffers i
  | .scratch => []

/-- Specification only: each step also states its proved real transition cost. -/
def step : Micro → Data → Option (Data × ℕ)
  | .pop _, ⟨[], _⟩ => none
  | .pop i, ⟨x :: xs, b⟩ =>
      some (⟨xs, Function.update b i (x ++ b i)⟩, 2 * x.length + 3)
  | .push i, ⟨xs, b⟩ =>
      some (⟨b i :: xs, Function.update b i []⟩, 2 * (b i).length + 4)
  | .copy i j, ⟨xs, b⟩ =>
      if i = j then none else
        some (⟨xs, Function.update b j (b i ++ b j)⟩, 2 * ((b i).length + 1))
  | .clear i, ⟨xs, b⟩ => some (⟨xs, Function.update b i []⟩, (b i).length + 1)

def run : List Micro → Data → Option (Data × ℕ)
  | [], d => some (d, 0)
  | op :: code, d => do
      let (d', t) ← step op d
      let (d'', u) ← run code d'
      pure (d'', t + u)

abbrev Label (code : List Micro) := (Fin (code.length + 1) × Fin 4) ⊕ Bool

/-- Program counters are finite; modulo is used only to construct labels. -/
def loc (code : List Micro) (pc : ℕ) (phase : Fin 4) : Label code :=
  .inl (⟨pc % (code.length + 1), Nat.mod_lt _ (by omega)⟩, phase)

/-- Actual bit-level implementations of the four microinstruction families. -/
def microStmt {Λ : Type} (op : Micro) (phase : Fin 4)
    (lab : Fin 4 → Λ) (next missing bad : Λ) : Stmt Key Λ Unit :=
  match op with
  | .pop i =>
      if phase = 0 then StackWord.markerStmt .data (lab 1) missing bad
      else if phase = 1 then GraphPreprocessing.Frame.scanStmt .data .scratch (lab 1) (lab 2) bad
      else if phase = 2 then copyMoveStmt .scratch (.buffer i) (lab 2) next
      else .goto (fun _ => bad)
  | .push i =>
      if phase = 0 then copyMoveStmt (.buffer i) .scratch (lab 0) (lab 1)
      else if phase = 1 then FixedFieldMachines.FrameEmit.delimiterStmt .data (lab 2)
      else if phase = 2 then FixedFieldMachines.FrameEmit.emitStmt .scratch .data (lab 2) (lab 3)
      else StackWord.consStmt .data next
  | .copy i j =>
      if i = j then .goto (fun _ => bad)
      else if phase = 0 then copyMoveStmt (.buffer i) .scratch (lab 0) (lab 1)
      else if phase = 1 then copyRestoreStmt (.buffer i) (.buffer j) .scratch (lab 1) next
      else .goto (fun _ => bad)
  | .clear i => clearStmt (.buffer i) (lab 0) next

def program (code : List Micro) : Label code → Stmt Key (Label code) Unit
  | .inr _ => .halt
  | .inl (pc, phase) => match code[pc.val]? with
    | none => .halt
    | some op => microStmt op phase (loc code pc.val) (loc code (pc.val + 1) 0) (.inr false) (.inr true)

abbrev machine (code : List Micro) : BinaryCompose.Machine where
  K := Key
  input := .data
  output := .data
  Label := Label code
  main := loc code 0 0
  State := Option Bool × Unit
  initial := (none, ())
  program := program code

/-- Actual dispatch lab a valid static instruction address. -/
theorem program_at (code : List Micro) (pc : ℕ) (op : Micro)
    (hpc : pc < code.length) (h : code[pc]? = some op) (phase : Fin 4) :
    program code (loc code pc phase) =
      microStmt op phase (loc code pc) (loc code (pc + 1) 0) (.inr false) (.inr true) := by
  simp [program, loc, Nat.mod_eq_of_lt (show pc < code.length + 1 by omega), h]

/-- The following operational contract is proved from real bit-stack loops. -/
theorem micro_exact {Λ : Type} (transition : Cfg Key Λ Unit → Option (Cfg Key Λ Unit))
    (op : Micro) (lab : Fin 4 → Λ) (next missing bad : Λ)
    (h : ∀ phase, ExecutesAt transition (lab phase) (microStmt op phase lab next missing bad))
    (d d' : Data) (time : ℕ) (hs : step op d = some (d', time)) :
    RunsExactly transition (cfg (lab 0) () (tapes d)) (cfg next () (tapes d')) time := by
  rcases d with ⟨xs, b⟩
  cases op with
  | pop i =>
    cases xs with
    | nil => simp [step] at hs
    | cons x xs =>
      cases Option.some.inj hs
      have hm : ExecutesAt transition (lab 0) (StackWord.markerStmt .data (lab 1) missing bad) := by
        simpa [microStmt] using h 0
      have hscan : ExecutesAt transition (lab 1)
          (GraphPreprocessing.Frame.scanStmt .data .scratch (lab 1) (lab 2) bad) := by
        simpa [microStmt] using h 1
      have hr : ExecutesAt transition (lab 2) (copyMoveStmt .scratch (.buffer i) (lab 2) next) := by
        simpa [microStmt] using h 2
      have run := StackWord.pop_exact Key.data (.buffer i) .scratch
        (by simp) (by simp) (by simp) transition (lab 0) (lab 1) (lab 2) next missing bad
        hm hscan hr () (tapes ⟨xs, b⟩) x ((stackEncoding wordEncoding).encode xs) (b i)
      convert run using 1 <;> congr 1 <;> funext k <;> cases k with
      | data => rfl
      | scratch => rfl
      | buffer j =>
        by_cases hji : j = i <;> simp [tapes, tapes3, Function.update, hji]
  | push i =>
    cases Option.some.inj hs
    have hm : ExecutesAt transition (lab 0) (copyMoveStmt (.buffer i) .scratch (lab 0) (lab 1)) := by
      simpa [microStmt] using h 0
    have hd : ExecutesAt transition (lab 1) (FixedFieldMachines.FrameEmit.delimiterStmt .data (lab 2)) := by
      simpa [microStmt] using h 1
    have he : ExecutesAt transition (lab 2) (FixedFieldMachines.FrameEmit.emitStmt .scratch .data (lab 2) (lab 3)) := by
      simpa [microStmt] using h 2
    have hk : ExecutesAt transition (lab 3) (StackWord.consStmt .data next) := by
      simpa [microStmt] using h 3
    have run := StackWord.push_exact (.buffer i) Key.data .scratch
      (by simp) (by simp) (by simp) transition (lab 0) (lab 1) (lab 2) (lab 3) next
      hm hd he hk () (tapes ⟨xs, b⟩) (b i) ((stackEncoding wordEncoding).encode xs)
    convert run using 1 <;> congr 1 <;> funext k <;> cases k with
    | data => rfl
    | scratch => rfl
    | buffer j =>
        by_cases hji : j = i <;> simp [tapes, tapes3, Function.update, hji]
  | copy i j =>
    by_cases hij : i = j
    · simp [step, hij] at hs
    · simp only [step, ite_eq_right hij] at hs
      cases Option.some.inj hs
      have hm : ExecutesAt transition (lab 0) (copyMoveStmt (.buffer i) .scratch (lab 0) (lab 1)) := by
        simpa [microStmt, hij] using h 0
      have hr : ExecutesAt transition (lab 1) (copyRestoreStmt (.buffer i) (.buffer j) .scratch (lab 1) next) := by
        simpa [microStmt, hij] using h 1
      have run := copy_exact_frame (Key.buffer i) (.buffer j) .scratch
        (by simpa using hij) (by simp) (by simp) transition (lab 0) (lab 1) next hm hr
        () (tapes ⟨xs, b⟩) (b i) (b j)
      convert run using 1 <;> congr 1 <;> funext k <;> cases k with
      | data => rfl
      | scratch => rfl
      | buffer k =>
        by_cases hki : k = i <;> by_cases hkj : k = j <;>
          simp_all [tapes, tapes3, Function.update]
  | clear i =>
    cases Option.some.inj hs
    have hc : ExecutesAt transition (lab 0) (clearStmt (.buffer i) (lab 0) next) := by
      simpa [microStmt] using h 0
    have run := clear_exact transition (.buffer i) (lab 0) next hc () (tapes ⟨xs, b⟩)
    convert run using 1 <;> congr 1 <;> funext k <;> cases k with
    | data => rfl
    | scratch => rfl
    | buffer j => simp [tapes, Function.update]

/-- Local dispatch installs the concrete microinstruction bit loops. -/
theorem instruction_exact (code : List Micro) (pc : ℕ) (op : Micro)
    (hpc : pc < code.length) (hop : code[pc]? = some op)
    (d d' : Data) (time : ℕ) (hs : step op d = some (d', time)) :
    RunsExactly (machine code).computer.step
      (cfg (loc code pc 0) () (tapes d))
      (cfg (loc code (pc + 1) 0) () (tapes d')) time := by
  apply micro_exact _ op (loc code pc) (loc code (pc + 1) 0) (.inr false) (.inr true) _ d d' time hs
  intro phase
  exact executesAt_tm2 _ _ _ (program_at code pc op hpc hop phase)

/-- Every successful semantic microprogram has the exact actual transition trace.
The semantics is not an instruction: the proof composes the concrete bit loops. -/
theorem run_exact (code pre rest : List Micro) (hc : code = pre ++ rest)
    (d d' : Data) (time : ℕ) (hs : run rest d = some (d', time)) :
    RunsExactly (machine code).computer.step
      (cfg (loc code pre.length 0) () (tapes d))
      (cfg (loc code code.length 0) () (tapes d')) time := by
  induction rest generalizing pre d d' time with
  | nil =>
    simp only [run, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    simp only [List.append_nil] at hc
    subst code
    rfl
  | cons op rest ih =>
    cases hm : step op d with
    | none => simp [run, hm] at hs
    | some pair =>
      rcases pair with ⟨middle, firstTime⟩
      cases ht : run rest middle with
      | none => simp [run, hm, ht] at hs
      | some pair =>
        rcases pair with ⟨last, restTime⟩
        have hp : (last, firstTime + restTime) = (d', time) := by
          simpa [run, hm, ht] using hs
        cases hp
        have hpc : pre.length < code.length := by simp [hc]
        have hop : code[pre.length]? = some op := by simp [hc]
        have first := instruction_exact code pre.length op hpc hop d middle firstTime hm
        have second := ih (pre ++ [op]) (by simpa [List.append_assoc] using hc)
          middle d' restTime ht
        simp only [List.length_append, List.length_singleton] at second
        convert first.trans second using 1
        omega

/-- The final static address really halts; no source instructions remain. -/
theorem program_done (code : List Micro) : program code (loc code code.length 0) = .halt := by
  simp [program, loc, Nat.mod_eq_of_lt (show code.length < code.length + 1 by omega)]

/-- Constants in the primitive budget do not depend on encoded word lengths. -/
theorem microStmt_budget {Λ : Type} (op : Micro) (phase : Fin 4)
    (lab : Fin 4 → Λ) (next missing bad : Λ) :
    TM2Cost.budget (microStmt op phase lab next missing bad) ≤ 8 := by
  cases op with
  | pop i => fin_cases phase <;> simp [microStmt, StackWord.markerStmt, TM2Cost.budget]
  | push i => fin_cases phase <;> simp [microStmt, StackWord.consStmt,
      FixedFieldMachines.FrameEmit.delimiterStmt, TM2Cost.budget]
  | copy i j =>
    by_cases hij : i = j
    · simp [microStmt, hij, TM2Cost.budget]
    · fin_cases phase <;> simp [microStmt, hij, TM2Cost.budget]
  | clear i => simp [microStmt]

/-- All interpreter work buffers start and finish empty. -/
def clean (s : List (List Bool)) : Data := ⟨s, fun _ => []⟩

/-- A fixed bounded list of distinct raw-word buffer keys. -/
def slots (i : Fin 8) : List (Fin 9) :=
  (List.finRange (i.val + 1)).map (fun j => ⟨j.val, by omega⟩)

/-- Pop a bounded prefix once, duplicate its last word, restore the prefix,
then insert the selected copy above it. Buffer eight is the fixed extra slot. -/
def copyCode (i : Fin 8) : List Micro :=
  (slots i).map Micro.pop ++ [.copy i.castSucc 8] ++
    ((slots i).reverse.map Micro.push) ++ [.push 8]

/-- Erase the selected raw word and restore exactly its preceding prefix. -/
def eraseCode (i : Fin 8) : List Micro :=
  (slots i).map Micro.pop ++ [.clear i.castSucc] ++
    ((slots i).dropLast.reverse.map Micro.push)

def swapCode : List Micro := [.pop 0, .pop 1, .push 0, .push 1]

@[simp] theorem copyCode_length (i : Fin 8) : (copyCode i).length = 2 * i.val + 4 := by
  simp [copyCode, slots]
  omega

@[simp] theorem eraseCode_length (i : Fin 8) : (eraseCode i).length = 2 * i.val + 2 := by
  simp [eraseCode, slots]
  omega

/-- Bound independent of all encoded values and input stack height. -/
theorem rearrangement_microinstructions_le (i : Fin 8) :
    (copyCode i).length ≤ 18 ∧ (eraseCode i).length ≤ 16 := by
  rw [copyCode_length, eraseCode_length]
  have := i.isLt
  omega

/-- All raw words, including caller-supplied initial data, satisfy this bound. -/
def Small (W : ℕ) (d : Data) : Prop :=
  (∀ word ∈ d.stack, word.length ≤ W) ∧ ∀ i, (d.buffers i).length ≤ W

theorem step_small_time (op : Micro) (d d' : Data) (time W : ℕ)
    (h : Small W d) (hs : step op d = some (d', time)) :
    Small (2 * W) d' ∧ time ≤ 2 * W + 4 := by
  rcases d with ⟨xs, b⟩
  rcases h with ⟨hx, hb⟩
  dsimp only at hx hb
  cases op with
  | pop i =>
    cases xs with
    | nil => simp [step] at hs
    | cons x xs =>
      cases Option.some.inj hs
      have hlen := hx x (by simp)
      refine ⟨⟨?_, ?_⟩, by omega⟩
      · intro word hw
        have := hx word (by simp [hw])
        omega
      · intro j
        by_cases hji : j = i
        · subst j; simp only [Function.update_self, List.length_append]; have := hb i; omega
        · simp only [Function.update_of_ne hji]; have := hb j; omega
  | push i =>
    cases Option.some.inj hs
    refine ⟨⟨?_, ?_⟩, by have := hb i; omega⟩
    · intro word hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · have := hb i; omega
      · have := hx word hw; omega
    · intro j
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]; have := hb j; omega
  | copy i j =>
    by_cases hij : i = j
    · simp [step, hij] at hs
    · simp only [step, ite_eq_right hij] at hs
      cases Option.some.inj hs
      refine ⟨⟨?_, ?_⟩, by have := hb i; omega⟩
      · intro word hw; have := hx word hw; omega
      · intro k
        by_cases hkj : k = j
        · subst k
          simp only [Function.update_self, List.length_append]
          have := hb i; have := hb j; omega
        · simp only [Function.update_of_ne hkj]; have := hb k; omega
  | clear i =>
    cases Option.some.inj hs
    refine ⟨⟨?_, ?_⟩, by have := hb i; omega⟩
    · intro word hw; have := hx word hw; omega
    · intro j
      by_cases hji : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hji]; have := hb j; omega

/-- A conservative real runtime bound. For the fixed Fin8 macros below the
exponent is at most eighteen, hence a fixed constant, independent of bytecode. -/
theorem run_time_le (code : List Micro) (d d' : Data) (time W : ℕ)
    (h : Small W d) (hs : run code d = some (d', time)) :
    time + (2 * W + 4) ≤ (2 * W + 4) * 2 ^ code.length := by
  induction code generalizing d d' time W with
  | nil =>
    have hp : (d, 0) = (d', time) := Option.some.inj hs
    cases hp
    simp
  | cons op code ih =>
    cases hm : step op d with
    | none => simp [run, hm] at hs
    | some pair =>
      rcases pair with ⟨middle, firstTime⟩
      cases ht : run code middle with
      | none => simp [run, hm, ht] at hs
      | some pair =>
        rcases pair with ⟨last, restTime⟩
        have hp : (last, firstTime + restTime) = (d', time) := by simpa [run, hm, ht] using hs
        cases hp
        rcases step_small_time op d middle firstTime W h hm with ⟨hmiddle, hfirst⟩
        have hrest := ih middle d' restTime (2 * W) hmiddle ht
        have hpow : 1 ≤ 2 ^ code.length := Nat.one_le_pow _ _ (by decide)
        simp only [List.length_cons, pow_succ]
        nlinarith

/-- Clean successful static microprogram execution includes its halting transition. -/
theorem run_clean_exact (code : List Micro) (s t : List (List Bool)) (time : ℕ)
    (h : run code (clean s) = some (clean t, time)) :
    RunsExactly (machine code).computer.step
      (initList (machine code).computer ((stackEncoding wordEncoding).encode s))
      (haltList (machine code).computer ((stackEncoding wordEncoding).encode t)) (time + 1) := by
  have hc (xs : List (List Bool)) : tapes (clean xs) =
      BinaryCompose.wordTape Key.data ((stackEncoding wordEncoding).encode xs) := by
    funext key; cases key <;> rfl
  have first := run_exact code [] code (by simp) (clean s) (clean t) time h
  have last : (machine code).computer.step (cfg (loc code code.length 0) () (tapes (clean t))) =
      some (haltList (machine code).computer ((stackEncoding wordEncoding).encode t)) := by
    change some (TM2.stepAux (program code (loc code code.length 0)) (none, ()) _) = _
    rw [program_done, BinaryCompose.Machine.halt_eq, hc]
    rfl
  have whole := first.trans (runsExactly_one last)
  rw [BinaryCompose.Machine.init_eq]
  simpa only [List.length_nil, hc, cfg, Nat.add_comm] using whole

end Holant.OneHot.StackProgram.Machine.Rearrange
