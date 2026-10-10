import Holant.Complexity.OracleOneQuery.ContextProgram
import Mathlib.Tactic.FinCases

/-! Three actual oracle calls between two ordinary Boolean-stack programs.
The protocol retains an arbitrary suffix, and emits each answer with the literal
pair codec. Its only unbounded operations are proved finite stack loops. -/
namespace Holant.Complexity.UniversalPairReduction.ThreeQuery
open Turing Computability BinaryCompose Holant.Algebraic StackProtocol

variable (a b : BinaryCompose.Machine)
abbrev Keys := a.K ⊕ (b.K ⊕ Fin 3)
abbrev States := Option Bool × (a.State × b.State)
abbrev Labels := a.Label ⊕ (b.Label ⊕ Fin 21)
abbrev Config := TM2.Cfg (fun _ : Keys a b => Bool) (Labels a b) (States a b)
def firstLabel (l : a.Label) : Labels a b := .inl l
def secondLabel (l : b.Label) : Labels a b := .inr (.inl l)
def admin (i : Fin 21) : Labels a b := .inr (.inr i)
def sourceKey : Keys a b := .inl a.output
def queryKey : Keys a b := .inr (.inl b.input)
def temporaryKey : Keys a b := .inr (.inr 0)
def savedOneKey : Keys a b := .inr (.inr 1)
def savedTwoKey : Keys a b := .inr (.inr 2)

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

def protocol (i : Fin 21) : OracleCommand (Keys a b) (Labels a b) (States a b) :=
  if i = 0 then .ordinary (GraphPreprocessing.Frame.scanStmt (sourceKey a b) (temporaryKey a b) (admin a b 0) (admin a b 1) (admin a b 20))
  else if i = 1 then .ordinary (copyMoveStmt (temporaryKey a b) (queryKey a b) (admin a b 1) (admin a b 2))
  else if i = 2 then .query (fun _ => admin a b 3)
  else if i = 3 then .ordinary (copyMoveStmt (queryKey a b) (savedOneKey a b) (admin a b 3) (admin a b 4))
  else if i = 4 then .ordinary (GraphPreprocessing.Frame.scanStmt (sourceKey a b) (temporaryKey a b) (admin a b 4) (admin a b 5) (admin a b 20))
  else if i = 5 then .ordinary (copyMoveStmt (temporaryKey a b) (queryKey a b) (admin a b 5) (admin a b 6))
  else if i = 6 then .query (fun _ => admin a b 7)
  else if i = 7 then .ordinary (copyMoveStmt (queryKey a b) (savedTwoKey a b) (admin a b 7) (admin a b 8))
  else if i = 8 then .ordinary (GraphPreprocessing.Frame.scanStmt (sourceKey a b) (temporaryKey a b) (admin a b 8) (admin a b 9) (admin a b 20))
  else if i = 9 then .ordinary (copyMoveStmt (temporaryKey a b) (queryKey a b) (admin a b 9) (admin a b 10))
  else if i = 10 then .query (fun _ => admin a b 11)
  else if i = 11 then .ordinary (copyMoveStmt (queryKey a b) (temporaryKey a b) (admin a b 11) (admin a b 12))
  else if i = 12 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt (sourceKey a b) (admin a b 13))
  else if i = 13 then .ordinary (FixedFieldMachines.FrameEmit.emitStmt (temporaryKey a b) (sourceKey a b) (admin a b 13) (admin a b 14))
  else if i = 14 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt (sourceKey a b) (admin a b 15))
  else if i = 15 then .ordinary (FixedFieldMachines.FrameEmit.emitStmt (savedTwoKey a b) (sourceKey a b) (admin a b 15) (admin a b 16))
  else if i = 16 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt (sourceKey a b) (admin a b 17))
  else if i = 17 then .ordinary (FixedFieldMachines.FrameEmit.emitStmt (savedOneKey a b) (sourceKey a b) (admin a b 17) (admin a b 18))
  else if i = 18 then .ordinary (copyMoveStmt (sourceKey a b) (temporaryKey a b) (admin a b 18) (admin a b 19))
  else if i = 19 then .ordinary (copyMoveStmt (temporaryKey a b) (queryKey a b) (admin a b 19) (secondLabel a b b.main))
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

def tapes (source query temporary savedOne savedTwo : List Bool) : Keys a b → List Bool :=
  tapes3 (Function.update (wordTape (savedOneKey a b) savedOne) (savedTwoKey a b) savedTwo)
    (sourceKey a b) (queryKey a b) (temporaryKey a b) source query temporary

def stageCfg (i : Fin 21) (source query temporary savedOne savedTwo : List Bool) : Config a b :=
  cfg (admin a b i) (a.initial,b.initial) (tapes a b source query temporary savedOne savedTwo)

private theorem tapes_empty (word : List Bool) :
    tapes a b word [] [] [] [] = wordTape (sourceKey a b) word := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,Function.update]

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


@[simp] theorem update_sourceKey (source query temporary savedOne savedTwo word : List Bool) :
    Function.update (tapes a b source query temporary savedOne savedTwo) (sourceKey a b) word =
      tapes a b word query temporary savedOne savedTwo := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,Function.update]

@[simp] theorem read_sourceKey (source query temporary savedOne savedTwo : List Bool) :
    tapes a b source query temporary savedOne savedTwo (sourceKey a b) = source := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey]

@[simp] theorem update_queryKey (source query temporary savedOne savedTwo word : List Bool) :
    Function.update (tapes a b source query temporary savedOne savedTwo) (queryKey a b) word =
      tapes a b source word temporary savedOne savedTwo := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,Function.update]

@[simp] theorem read_queryKey (source query temporary savedOne savedTwo : List Bool) :
    tapes a b source query temporary savedOne savedTwo (queryKey a b) = query := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey]

@[simp] theorem update_temporaryKey (source query temporary savedOne savedTwo word : List Bool) :
    Function.update (tapes a b source query temporary savedOne savedTwo) (temporaryKey a b) word =
      tapes a b source query word savedOne savedTwo := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,Function.update]

@[simp] theorem read_temporaryKey (source query temporary savedOne savedTwo : List Bool) :
    tapes a b source query temporary savedOne savedTwo (temporaryKey a b) = temporary := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey]

@[simp] theorem update_savedOneKey (source query temporary savedOne savedTwo word : List Bool) :
    Function.update (tapes a b source query temporary savedOne savedTwo) (savedOneKey a b) word =
      tapes a b source query temporary word savedTwo := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,Function.update]

@[simp] theorem read_savedOneKey (source query temporary savedOne savedTwo : List Bool) :
    tapes a b source query temporary savedOne savedTwo (savedOneKey a b) = savedOne := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey]

@[simp] theorem update_savedTwoKey (source query temporary savedOne savedTwo word : List Bool) :
    Function.update (tapes a b source query temporary savedOne savedTwo) (savedTwoKey a b) word =
      tapes a b source query temporary savedOne word := by
  funext k
  rcases k with k | k
  · by_cases h : k = a.output <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
  · rcases k with k | k
    · by_cases h : k = b.input <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,h]
    · fin_cases k <;> simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey,Function.update]

@[simp] theorem read_savedTwoKey (source query temporary savedOne savedTwo : List Bool) :
    tapes a b source query temporary savedOne savedTwo (savedTwoKey a b) = savedTwo := by
  simp [tapes,tapes3,wordTape,sourceKey,queryKey,temporaryKey,savedOneKey,savedTwoKey]

/-- Both extraction loops are literal TM2 transitions and preserve saved answers. -/
theorem extract_run (oracle : List Bool → List Bool) (scan restore next : Fin 21)
    (hs : protocol a b scan = .ordinary (GraphPreprocessing.Frame.scanStmt
      (sourceKey a b) (temporaryKey a b) (admin a b scan) (admin a b restore) (admin a b 20)))
    (hr : protocol a b restore = .ordinary (copyMoveStmt
      (temporaryKey a b) (queryKey a b) (admin a b restore) (admin a b next)))
    (word suffix one two : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b scan (frame word ++ suffix) [] [] one two)
      (stageCfg a b next suffix word [] one two) (2 * (word.length + 1)) := by
  have h := GraphPreprocessing.Frame.extract_exact (sourceKey a b) (queryKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b scan) (admin a b restore) (admin a b next) (admin a b 20)
    (by intro state ts; simp [machine,OracleMachine.step,program,admin,hs])
    (by intro state ts; simp [machine,OracleMachine.step,program,admin,hr])
    (a.initial,b.initial) (tapes a b [] [] [] one two) word suffix []
  simpa only [tapes3,update_sourceKey,update_queryKey,update_temporaryKey,List.append_nil,stageCfg] using h

theorem query_run (oracle : List Bool → List Bool) (call next : Fin 21)
    (hq : protocol a b call = .query (fun _ => admin a b next))
    (source word one two : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b call source word [] one two)
      (stageCfg a b next source (oracle word) [] one two) 1 := by
  apply runsExactly_one
  simp [stageCfg,cfg,machine,OracleMachine.step,program,admin,hq]

theorem save_one_run (oracle : List Bool → List Bool) (source answer two : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 3 source answer [] [] two)
      (stageCfg a b 4 source [] [] answer.reverse two) (answer.length + 1) := by
  have h := copy_move_exact (queryKey a b) (sourceKey a b) (savedOneKey a b)
    (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 3) (admin a b 4)
    (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] [] two) answer source []
  simpa only [tapes3,update_queryKey,update_sourceKey,update_savedOneKey,List.append_nil,stageCfg] using h

theorem save_two_run (oracle : List Bool → List Bool) (source answer one : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 7 source answer [] one [])
      (stageCfg a b 8 source [] [] one answer.reverse) (answer.length + 1) := by
  have h := copy_move_exact (queryKey a b) (sourceKey a b) (savedTwoKey a b)
    (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 7) (admin a b 8)
    (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] one []) answer source []
  simpa only [tapes3,update_queryKey,update_sourceKey,update_savedTwoKey,List.append_nil,stageCfg] using h

theorem emit_third_run (oracle : List Bool → List Bool) (source answer one two : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 11 source answer [] one two)
      (stageCfg a b 14 (frame answer ++ source) [] [] one two) (2 * answer.length + 3) := by
  have h := FixedFieldMachines.FrameEmit.prepend_exact (queryKey a b) (sourceKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 11) (admin a b 12) (admin a b 13) (admin a b 14)
    (by intro state ts; rfl) (by intro state ts; rfl) (by intro state ts; rfl)
    (a.initial,b.initial) (tapes a b [] [] [] one two) answer source
  simpa only [tapes3,update_queryKey,update_sourceKey,update_temporaryKey,stageCfg] using h


theorem emit_two_run (oracle : List Bool → List Bool) (source answer one : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 14 source [] [] one answer.reverse)
      (stageCfg a b 16 (frame answer ++ source) [] [] one []) (answer.length + 2) := by
  have hd : RunsExactly ((machine a b).step oracle)
      (stageCfg a b 14 source [] [] one answer.reverse)
      (stageCfg a b 15 (false :: source) [] [] one answer.reverse) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,
      FixedFieldMachines.FrameEmit.delimiterStmt,TM2.stepAux]
  have h := FixedFieldMachines.FrameEmit.emit_exact (queryKey a b) (sourceKey a b) (savedTwoKey a b)
    (by intro h; cases h) ((machine a b).step oracle) (admin a b 15) (admin a b 16)
    (by intro state ts; rfl) (a.initial,b.initial) (tapes a b [] [] [] one []) [] (false :: source) answer.reverse
  simp only [tapes3,update_queryKey,update_sourceKey,update_savedTwoKey,
    List.reverse_reverse,List.length_reverse] at h
  have hw : FixedFieldMachines.FrameEmit.body answer ++ false :: source = frame answer ++ source := by
    rw [← FixedFieldMachines.FrameEmit.body_delimiter]
    simp only [List.append_assoc,List.singleton_append]
  rw [hw] at h
  exact hd.trans h

theorem emit_one_run (oracle : List Bool → List Bool) (source answer : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 16 source [] [] answer.reverse [])
      (stageCfg a b 18 (frame answer ++ source) [] [] [] []) (answer.length + 2) := by
  have hd : RunsExactly ((machine a b).step oracle)
      (stageCfg a b 16 source [] [] answer.reverse [])
      (stageCfg a b 17 (false :: source) [] [] answer.reverse []) 1 := by
    apply runsExactly_one
    simp [stageCfg,cfg,machine,OracleMachine.step,program,protocol,admin,
      FixedFieldMachines.FrameEmit.delimiterStmt,TM2.stepAux]
  have h := FixedFieldMachines.FrameEmit.emit_exact (queryKey a b) (sourceKey a b) (savedOneKey a b)
    (by intro h; cases h) ((machine a b).step oracle) (admin a b 17) (admin a b 18)
    (by intro state ts; rfl) (a.initial,b.initial) (tapes a b [] [] [] [] []) [] (false :: source) answer.reverse
  simp only [tapes3,update_queryKey,update_sourceKey,update_savedOneKey,
    List.reverse_reverse,List.length_reverse] at h
  have hw : FixedFieldMachines.FrameEmit.body answer ++ false :: source = frame answer ++ source := by
    rw [← FixedFieldMachines.FrameEmit.body_delimiter]
    simp only [List.append_assoc,List.singleton_append]
  rw [hw] at h
  exact hd.trans h

/-- Three encoded oracle answers followed by the exact unchanged context bytes. -/
def word (x y z context : List Bool) : List Bool := frame x ++ (frame y ++ (frame z ++ context))

theorem collector_run (oracle : List Bool → List Bool) (x y z context : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (leftCfg a b (haltList a.computer (word x y z context)))
      (stageCfg a b 18 (word (oracle x) (oracle y) (oracle z) context) [] [] [] [])
      (2 * (x.length + y.length + z.length) +
        2 * ((oracle x).length + (oracle y).length + (oracle z).length) + 18) := by
  rw [left_halt]
  have e1 := extract_run a b oracle 0 1 2 rfl rfl x (frame y ++ (frame z ++ context)) [] []
  have q1 := query_run a b oracle 2 3 rfl (frame y ++ (frame z ++ context)) x [] []
  have s1 := save_one_run a b oracle (frame y ++ (frame z ++ context)) (oracle x) []
  have e2 := extract_run a b oracle 4 5 6 rfl rfl y (frame z ++ context) (oracle x).reverse []
  have q2 := query_run a b oracle 6 7 rfl (frame z ++ context) y (oracle x).reverse []
  have s2 := save_two_run a b oracle (frame z ++ context) (oracle y) (oracle x).reverse
  have e3 := extract_run a b oracle 8 9 10 rfl rfl z context (oracle x).reverse (oracle y).reverse
  have q3 := query_run a b oracle 10 11 rfl context z (oracle x).reverse (oracle y).reverse
  have s3 := emit_third_run a b oracle context (oracle z) (oracle x).reverse (oracle y).reverse
  have p2 := emit_two_run a b oracle (frame (oracle z) ++ context) (oracle y) (oracle x).reverse
  have p1 := emit_one_run a b oracle (frame (oracle y) ++ (frame (oracle z) ++ context)) (oracle x)
  have h := (((((((((e1.trans q1).trans s1).trans e2).trans q2).trans s2).trans e3).trans q3).trans s3).trans p2).trans p1
  convert h using 1 <;> (first | rfl | omega)

theorem transfer_run (oracle : List Bool → List Bool) (output : List Bool) :
    RunsExactly ((machine a b).step oracle)
      (stageCfg a b 18 output [] [] [] [])
      (rightCfg a b (initList b.computer output)) (2 * (output.length + 1)) := by
  rw [right_init]
  unfold stageCfg
  rw [tapes_empty]
  exact transfer_exact ((machine a b).step oracle)
    (sourceKey a b) (queryKey a b) (temporaryKey a b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (admin a b 18) (admin a b 19) (secondLabel a b b.main)
    (by intro state ts; rfl) (by intro state ts; rfl) (a.initial,b.initial) output

/-- The compiler, three-query collector, and decoder form one actual finite run. -/
theorem run (oracle : List Bool → List Bool) (input x y z context output : List Bool) (n m : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer (word x y z context)))
    (hb : (fun p => p.bind b.computer.step)^[m]
      (some (initList b.computer (word (oracle x) (oracle y) (oracle z) context))) =
      some (haltList b.computer output)) :
    (fun p => p.bind ((machine a b).step oracle))
      ^[m + (2 * ((word (oracle x) (oracle y) (oracle z) context).length + 1) +
        ((2 * (x.length+y.length+z.length) +
          2 * ((oracle x).length+(oracle y).length+(oracle z).length) + 18) + n))]
      (some ((machine a b).init input)) = some ((machine a b).output output) := by
  have hfirst := OracleOneQuery.ordinary_run (M := machine a b)
    (leftLayout a b) (leftStates a b) (firstLabel a b) (some (admin a b 0))
    (fun _ => rfl) oracle _ _ n ha
  have hlast := OracleOneQuery.ordinary_run (M := machine a b)
    (rightLayout a b) (rightStates a b) (secondLabel a b) none
    (fun _ => rfl) oracle _ _ m hb
  change (fun p => p.bind ((machine a b).step oracle))^[n]
    (some (leftCfg a b _)) = some (leftCfg a b _) at hfirst
  change (fun p => p.bind ((machine a b).step oracle))^[m]
    (some (rightCfg a b _)) = some (rightCfg a b _) at hlast
  rw [left_init] at hfirst
  rw [right_halt] at hlast
  rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
    hfirst,collector_run,transfer_run]
  exact hlast

def outputs (oracle : List Bool → List Bool) (input x y z context output : List Bool) (n m : ℕ)
    (ha : TM2OutputsInTime a.computer input (some (word x y z context)) n)
    (hb : TM2OutputsInTime b.computer (word (oracle x) (oracle y) (oracle z) context) (some output) m) :
    (machine a b).OutputsInTime oracle input output
      (n + (2 * (x.length+y.length+z.length) +
        2 * ((oracle x).length+(oracle y).length+(oracle z).length) + 18) +
        2 * ((word (oracle x) (oracle y) (oracle z) context).length + 1) + m) where
  steps := hb.steps + (2 * ((word (oracle x) (oracle y) (oracle z) context).length + 1) +
    ((2 * (x.length+y.length+z.length) +
      2 * ((oracle x).length+(oracle y).length+(oracle z).length) + 18) + ha.steps))
  evals_in_steps := run a b oracle input x y z context output ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  steps_le_m := by have := ha.steps_le_m; have := hb.steps_le_m; omega

end Holant.Complexity.UniversalPairReduction.ThreeQuery
