import Holant.Complexity.OracleOneQuery.ContextProgram
import Mathlib.Tactic.FinCases

/-! One fixed finite Boolean-stack program collects an input-dependent list of
actual oracle answers, retaining arbitrary context and clearing all scratch. -/
namespace Holant.Complexity.OracleBatch
open Turing Computability BinaryCompose Holant.Algebraic StackProtocol

variable (a b : BinaryCompose.Machine)
abbrev Keys := a.K ⊕ (b.K ⊕ Fin 3)
abbrev States := Option Bool × (a.State × b.State)
abbrev Labels := a.Label ⊕ (b.Label ⊕ Fin 17)
abbrev Config := TM2.Cfg (fun _ : Keys a b => Bool) (Labels a b) (States a b)
def firstLabel (l : a.Label) : Labels a b := .inl l
def secondLabel (l : b.Label) : Labels a b := .inr (.inl l)
def admin (i : Fin 17) : Labels a b := .inr (.inr i)
def sourceKey : Keys a b := .inl a.output
def queryKey : Keys a b := .inr (.inl b.input)
def temporaryKey : Keys a b := .inr (.inr 0)
def pendingKey : Keys a b := .inr (.inr 1)
def accumulatorKey : Keys a b := .inr (.inr 2)

def leftLayout : StackEmbedding a.K (Keys a b) where
  key := Sum.inl
  lift tapes := Sum.elim tapes (fun _ => [])
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl i => by_cases h : i = k <;> simp [Function.update, h, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
def rightLayout : StackEmbedding b.K (Keys a b) where
  key k := .inr (.inl k)
  lift tapes := Sum.elim (fun _ => []) (Sum.elim tapes (fun _ => []))
  lookup _ _ := rfl
  update tapes k word := by
    funext key
    cases key with
    | inl i => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
    | inr j =>
      cases j with
      | inl i => by_cases h : i = k <;> simp [Function.update, h, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
      | inr u => simp [Function.update, -Sum.elim_update_left, -Sum.update_elim_inl, -Sum.elim_update_right, -Sum.update_elim_inr]
def leftStates : StateEmbedding a.State (States a b) where
  put v := (none, v, b.initial)
  get v := v.2.1
  get_put _ := rfl
def rightStates : StateEmbedding b.State (States a b) where
  put v := (none, a.initial, v)
  get v := v.2.2
  get_put _ := rfl

/-- A list marker is consumed by one ordinary transition. -/
def dispatchStmt : StackProtocol.Stmt (Keys a b) (Labels a b) (a.State × b.State) :=
  .pop (pendingKey a b) (fun v bit => (bit,v.2))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (.load (fun v => (none,v.2)) (.goto (fun _ => admin a b 3)))
        (.load (fun v => (none,v.2)) (.goto (fun _ => admin a b 9))))
      (.load (fun v => (none,v.2)) (.goto (fun _ => admin a b 16))))

/-- Consume answer bits in order, pushing reversed framing pairs. -/
def reverseEmitStmt : StackProtocol.Stmt (Keys a b) (Labels a b) (a.State × b.State) :=
  .pop (queryKey a b) (fun v bit => (bit,v.2))
    (.branch (fun v => v.1.isSome)
      (.push (accumulatorKey a b) (fun _ => true)
        (.push (accumulatorKey a b) (fun v => v.1.getD false)
          (.load (fun v => (none,v.2)) (.goto (fun _ => admin a b 7)))))
      (.load (fun v => (none,v.2)) (.goto (fun _ => admin a b 8))))

def protocol (i : Fin 17) : OracleCommand (Keys a b) (Labels a b) (States a b) :=
  if i = 0 then .ordinary (GraphPreprocessing.Frame.scanStmt (sourceKey a b) (temporaryKey a b) (admin a b 0) (admin a b 1) (admin a b 16))
  else if i = 1 then .ordinary (copyMoveStmt (temporaryKey a b) (pendingKey a b) (admin a b 1) (admin a b 2))
  else if i = 2 then .ordinary (dispatchStmt a b)
  else if i = 3 then .ordinary (GraphPreprocessing.Frame.scanStmt (pendingKey a b) (temporaryKey a b) (admin a b 3) (admin a b 4) (admin a b 16))
  else if i = 4 then .ordinary (copyMoveStmt (temporaryKey a b) (queryKey a b) (admin a b 4) (admin a b 5))
  else if i = 5 then .query (fun _ => admin a b 6)
  else if i = 6 then .ordinary (.push (accumulatorKey a b) (fun _ => true) (.goto (fun _ => admin a b 7)))
  else if i = 7 then .ordinary (reverseEmitStmt a b)
  else if i = 8 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt (accumulatorKey a b) (admin a b 2))
  else if i = 9 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt (accumulatorKey a b) (admin a b 10))
  else if i = 10 then .ordinary (copyMoveStmt (accumulatorKey a b) (queryKey a b) (admin a b 10) (admin a b 11))
  else if i = 11 then .ordinary (copyMoveStmt (queryKey a b) (temporaryKey a b) (admin a b 11) (admin a b 12))
  else if i = 12 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt (sourceKey a b) (admin a b 13))
  else if i = 13 then .ordinary (FixedFieldMachines.FrameEmit.emitStmt (temporaryKey a b) (sourceKey a b) (admin a b 13) (admin a b 14))
  else if i = 14 then .ordinary (copyMoveStmt (sourceKey a b) (temporaryKey a b) (admin a b 14) (admin a b 15))
  else if i = 15 then .ordinary (copyMoveStmt (temporaryKey a b) (queryKey a b) (admin a b 15) (secondLabel a b b.main))
  else .ordinary .halt

def program : Labels a b → OracleCommand (Keys a b) (Labels a b) (States a b)
  | .inl l => .ordinary (embedStmt (leftLayout a b) (leftStates a b)
      (firstLabel a b) (some (admin a b 0)) (a.program l))
  | .inr (.inl l) => .ordinary (embedStmt (rightLayout a b) (rightStates a b)
      (secondLabel a b) none (b.program l))
  | .inr (.inr i) => protocol a b i

abbrev machine : OracleMachine where
  K := Keys a b
  inputStack := .inl a.input
  outputStack := .inr (.inl b.output)
  queryStack := queryKey a b
  answerStack := queryKey a b
  Λ := Labels a b
  main := firstLabel a b a.main
  σ := States a b
  initialState := (none, a.initial, b.initial)
  program := program a b

def leftCfg (c : a.Config) : Config a b :=
  embedCfg (leftLayout a b) (leftStates a b) (firstLabel a b) (some (admin a b 0)) c
def rightCfg (c : b.Config) : Config a b :=
  embedCfg (rightLayout a b) (rightStates a b) (secondLabel a b) none c

def tapes (source query temporary pending accumulator : List Bool) : Keys a b → List Bool :=
  tapes3 (Function.update (wordTape (pendingKey a b) pending) (accumulatorKey a b) accumulator)
    (sourceKey a b) (queryKey a b) (temporaryKey a b) source query temporary

def stageCfg (i : Fin 17) (source query temporary pending accumulator : List Bool) : Config a b :=
  cfg (admin a b i) (a.initial,b.initial) (tapes a b source query temporary pending accumulator)

theorem tapes_empty (word : List Bool) :
    tapes a b word [] [] [] [] = wordTape (sourceKey a b) word := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,Function.update]

@[simp] theorem left_wordTape (key : a.K) (word : List Bool) :
    (leftLayout a b).lift (wordTape key word) = wordTape (.inl key : Keys a b) word := by
  funext k
  cases k with
  | inl k => by_cases h : k = key <;> simp [leftLayout,wordTape,h]
  | inr k => simp [leftLayout,wordTape]
@[simp] theorem right_wordTape (key : b.K) (word : List Bool) :
    (rightLayout a b).lift (wordTape key word) = wordTape (.inr (.inl key) : Keys a b) word := by
  funext k
  cases k with
  | inl k => simp [rightLayout,wordTape]
  | inr k => cases k with
    | inl k => by_cases h : k = key <;> simp [rightLayout,wordTape,h]
    | inr k => simp [rightLayout,wordTape]

theorem left_init (input : List Bool) :
    leftCfg a b (initList a.computer input) = (machine a b).init input := by
  rw [a.init_eq]
  simp only [leftCfg,embedCfg,leftStates,Option.elim_some,left_wordTape,
    machine,OracleMachine.init,firstLabel]
  congr 1
  funext k
  simp [wordTape,Function.update]
theorem left_halt (word : List Bool) :
    leftCfg a b (haltList a.computer word) = stageCfg a b 0 word [] [] [] [] := by
  rw [a.halt_eq]
  simp [leftCfg,embedCfg,leftStates,stageCfg,cfg,tapes_empty,sourceKey]
theorem right_init (word : List Bool) :
    rightCfg a b (initList b.computer word) =
      cfg (secondLabel a b b.main) (a.initial,b.initial) (wordTape (queryKey a b) word) := by
  rw [b.init_eq]
  simp [rightCfg,embedCfg,rightStates,cfg,queryKey]
theorem right_halt (word : List Bool) :
    rightCfg a b (haltList b.computer word) = (machine a b).output word := by
  rw [b.halt_eq]
  simp only [rightCfg,embedCfg,rightStates,Option.elim_none,right_wordTape,machine,OracleMachine.output]
  congr 1
  funext k
  simp [wordTape,Function.update]


@[simp] theorem update_sourceKey (source query temporary pending accumulator word : List Bool) :
    Function.update (tapes a b source query temporary pending accumulator) (sourceKey a b) word =
      tapes a b word query temporary pending accumulator := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,Function.update]

@[simp] theorem read_sourceKey (source query temporary pending accumulator : List Bool) :
    tapes a b source query temporary pending accumulator (sourceKey a b) = source := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey]

@[simp] theorem update_queryKey (source query temporary pending accumulator word : List Bool) :
    Function.update (tapes a b source query temporary pending accumulator) (queryKey a b) word =
      tapes a b source word temporary pending accumulator := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,Function.update]

@[simp] theorem read_queryKey (source query temporary pending accumulator : List Bool) :
    tapes a b source query temporary pending accumulator (queryKey a b) = query := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey]

@[simp] theorem update_temporaryKey (source query temporary pending accumulator word : List Bool) :
    Function.update (tapes a b source query temporary pending accumulator) (temporaryKey a b) word =
      tapes a b source query word pending accumulator := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,Function.update]

@[simp] theorem read_temporaryKey (source query temporary pending accumulator : List Bool) :
    tapes a b source query temporary pending accumulator (temporaryKey a b) = temporary := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey]

@[simp] theorem update_pendingKey (source query temporary pending accumulator word : List Bool) :
    Function.update (tapes a b source query temporary pending accumulator) (pendingKey a b) word =
      tapes a b source query temporary word accumulator := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,Function.update]

@[simp] theorem read_pendingKey (source query temporary pending accumulator : List Bool) :
    tapes a b source query temporary pending accumulator (pendingKey a b) = pending := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey]

@[simp] theorem update_accumulatorKey (source query temporary pending accumulator word : List Bool) :
    Function.update (tapes a b source query temporary pending accumulator) (accumulatorKey a b) word =
      tapes a b source query temporary pending word := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey,Function.update]

@[simp] theorem read_accumulatorKey (source query temporary pending accumulator : List Bool) :
    tapes a b source query temporary pending accumulator (accumulatorKey a b) = accumulator := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,pendingKey,accumulatorKey]


end Holant.Complexity.OracleBatch
