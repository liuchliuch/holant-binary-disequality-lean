import Holant.Complexity.OracleOneQuery.Program
import Holant.Complexity.OracleOneQuery.FramedQuery
import Holant.Complexity.FixedFieldMachines.PairEncoding

/-! An actual one-query protocol preserving a separately encoded caller context.
The input compiler returns (query, context); only query is sent to the oracle;
the answer decoder receives (answer, context). -/
namespace Holant.Complexity.OracleOneQuery.Context
open Turing Computability BinaryCompose Holant.Algebraic

variable (a b : BinaryCompose.Machine)
abbrev Keys := BinaryCompose.Machine.Keys a b
abbrev States := BinaryCompose.Machine.States a b
abbrev Labels := a.Label ⊕ (b.Label ⊕ Fin 9)
abbrev Config := TM2.Cfg (fun _ : Keys a b => Bool) (Labels a b) (States a b)
def firstLabel (l : a.Label) : Labels a b := .inl l
def secondLabel (l : b.Label) : Labels a b := .inr (.inl l)
def admin (i : Fin 9) : Labels a b := .inr (.inr i)

def program : Labels a b → OracleCommand (Keys a b) (Labels a b) (States a b)
  | .inl l => .ordinary (embedStmt (a.leftLayout b) (a.leftStates b)
      (firstLabel a b) (some (admin a b 0)) (a.program l))
  | .inr (.inl l) => .ordinary (embedStmt (a.rightLayout b) (a.rightStates b)
      (secondLabel a b) none (b.program l))
  | .inr (.inr l) =>
    if l = 0 then .ordinary (GraphPreprocessing.Frame.scanStmt
      (a.sourceKey b) (a.temporaryKey b) (admin a b 0) (admin a b 1) (admin a b 8))
    else if l = 1 then .ordinary (StackProtocol.copyMoveStmt
      (a.temporaryKey b) (a.destinationKey b) (admin a b 1) (admin a b 2))
    else if l = 2 then .query (fun _ => admin a b 3)
    else if l = 3 then .ordinary (StackProtocol.copyMoveStmt
      (a.destinationKey b) (a.temporaryKey b) (admin a b 3) (admin a b 4))
    else if l = 4 then .ordinary (FixedFieldMachines.FrameEmit.delimiterStmt
      (a.sourceKey b) (admin a b 5))
    else if l = 5 then .ordinary (FixedFieldMachines.FrameEmit.emitStmt
      (a.temporaryKey b) (a.sourceKey b) (admin a b 5) (admin a b 6))
    else if l = 6 then .ordinary (StackProtocol.copyMoveStmt
      (a.sourceKey b) (a.temporaryKey b) (admin a b 6) (admin a b 7))
    else if l = 7 then .ordinary (StackProtocol.copyMoveStmt
      (a.temporaryKey b) (a.destinationKey b) (admin a b 7) (secondLabel a b b.main))
    else .ordinary .halt

abbrev machine : OracleMachine where
  K := Keys a b
  inputStack := .inl a.input
  outputStack := .inr (.inl b.output)
  queryStack := a.destinationKey b
  answerStack := a.destinationKey b
  Λ := Labels a b
  main := firstLabel a b a.main
  σ := States a b
  initialState := (none, a.initial, b.initial)
  program := program a b

def leftCfg (c : a.Config) : Config a b :=
  embedCfg (a.leftLayout b) (a.leftStates b) (firstLabel a b) (some (admin a b 0)) c

def rightCfg (c : b.Config) : Config a b :=
  embedCfg (a.rightLayout b) (a.rightStates b) (secondLabel a b) none c

theorem left_init (input : List Bool) :
    leftCfg a b (initList a.computer input) = (machine a b).init input := by
  rw [a.init_eq]
  simp only [leftCfg, embedCfg, Machine.leftStates, Option.elim_some,
    Machine.left_wordTape, machine, OracleMachine.init, firstLabel]
  congr 1
  funext k
  simp [wordTape, Function.update]

theorem left_halt (word : List Bool) :
    leftCfg a b (haltList a.computer word) =
      StackProtocol.cfg (admin a b 0) (a.initial, b.initial)
        (wordTape (a.sourceKey b) word) := by
  rw [a.halt_eq]
  simp [leftCfg, embedCfg, Machine.leftStates, StackProtocol.cfg, Machine.sourceKey]

theorem right_init (word : List Bool) :
    rightCfg a b (initList b.computer word) =
      StackProtocol.cfg (secondLabel a b b.main) (a.initial, b.initial)
        (wordTape (a.destinationKey b) word) := by
  rw [b.init_eq]
  simp [rightCfg, embedCfg, Machine.rightStates, StackProtocol.cfg, Machine.destinationKey]

theorem right_halt (word : List Bool) :
    rightCfg a b (haltList b.computer word) = (machine a b).output word := by
  rw [b.halt_eq]
  simp only [rightCfg, embedCfg, Machine.rightStates, Option.elim_none,
    Machine.right_wordTape, machine, OracleMachine.output]
  congr 1
  funext k
  simp [wordTape, Function.update]


private theorem empty_tapes (word : List Bool) :
    StackProtocol.tapes3 (fun _ : Keys a b => []) (a.sourceKey b)
      (a.destinationKey b) (a.temporaryKey b) word [] [] =
        wordTape (a.sourceKey b) word := by
  funext k
  cases k with
  | inl k => simp [StackProtocol.tapes3, Machine.sourceKey, Machine.destinationKey,
      Machine.temporaryKey, wordTape, Function.update_apply]
  | inr k => cases k <;> simp [StackProtocol.tapes3, Machine.sourceKey,
      Machine.destinationKey, Machine.temporaryKey, wordTape, Function.update_apply]

/-- The protocol exposes only the first word, retains arbitrary context bytes,
and returns a framed answer/context pair with every other tape cleared. -/
theorem query_run (oracle : List Bool → List Bool) (query context : List Bool) :
    StackProtocol.RunsExactly ((machine a b).step oracle)
      (leftCfg a b (haltList a.computer (frame query ++ context)))
      (StackProtocol.cfg (admin a b 6) (a.initial, b.initial)
        (wordTape (a.sourceKey b) (frame (oracle query) ++ context)))
      (2 * query.length + 2 * (oracle query).length + 6) := by
  rw [left_halt]
  have h := FramedQuery.exact_run (a.sourceKey b) (a.destinationKey b) (a.temporaryKey b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    ((machine a b).step oracle) (admin a b 0) (admin a b 1) (admin a b 2)
    (admin a b 3) (admin a b 4) (admin a b 5) (admin a b 6) (admin a b 8)
    (by intro state tapes; rfl) (by intro state tapes; rfl)
    oracle (by intro state tapes; rfl)
    (by intro state tapes; rfl) (by intro state tapes; rfl) (by intro state tapes; rfl)
    (a.initial, b.initial) (fun _ => []) query context
  simpa only [empty_tapes] using h

theorem transfer_run (oracle : List Bool → List Bool) (word : List Bool) :
    StackProtocol.RunsExactly ((machine a b).step oracle)
      (StackProtocol.cfg (admin a b 6) (a.initial, b.initial)
        (wordTape (a.sourceKey b) word))
      (rightCfg a b (initList b.computer word)) (2 * (word.length + 1)) := by
  rw [right_init]
  exact transfer_exact ((machine a b).step oracle)
    (a.sourceKey b) (a.destinationKey b) (a.temporaryKey b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (admin a b 6) (admin a b 7) (secondLabel a b b.main)
    (by intro state tapes; rfl) (by intro state tapes; rfl)
    (a.initial, b.initial) word

/-- Full ordinary compiler / single oracle query / ordinary answer-decoder run. -/
theorem run (oracle : List Bool → List Bool)
    (input query context output : List Bool) (n m : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer (frame query ++ context)))
    (hb : (fun p => p.bind b.computer.step)^[m]
      (some (initList b.computer (frame (oracle query) ++ context))) =
        some (haltList b.computer output)) :
    (fun p => p.bind ((machine a b).step oracle))
      ^[m + (2 * ((frame (oracle query) ++ context).length + 1) +
        ((2 * query.length + 2 * (oracle query).length + 6) + n))]
      (some ((machine a b).init input)) = some ((machine a b).output output) := by
  have hfirst := ordinary_run (M := machine a b) (a.leftLayout b) (a.leftStates b)
    (firstLabel a b) (some (admin a b 0)) (fun _ => rfl) oracle _ _ n ha
  have hlast := ordinary_run (M := machine a b) (a.rightLayout b) (a.rightStates b)
    (secondLabel a b) none (fun _ => rfl) oracle _ _ m hb
  change (fun p => p.bind ((machine a b).step oracle))^[n]
    (some (leftCfg a b _)) = some (leftCfg a b _) at hfirst
  change (fun p => p.bind ((machine a b).step oracle))^[m]
    (some (rightCfg a b _)) = some (rightCfg a b _) at hlast
  rw [left_init] at hfirst
  rw [right_halt] at hlast
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hfirst, query_run, transfer_run]
  exact hlast

def outputs (oracle : List Bool → List Bool)
    (input query context output : List Bool) (n m : ℕ)
    (ha : TM2OutputsInTime a.computer input (some (frame query ++ context)) n)
    (hb : TM2OutputsInTime b.computer (frame (oracle query) ++ context) (some output) m) :
    (machine a b).OutputsInTime oracle input output
      (n + (2 * query.length + 2 * (oracle query).length + 6) +
        2 * ((frame (oracle query) ++ context).length + 1) + m) where
  steps := hb.steps + (2 * ((frame (oracle query) ++ context).length + 1) +
    ((2 * query.length + 2 * (oracle query).length + 6) + ha.steps))
  evals_in_steps := run a b oracle input query context output ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  steps_le_m := by have := ha.steps_le_m; have := hb.steps_le_m; omega

end Holant.Complexity.OracleOneQuery.Context
