import Holant.Complexity.BinaryCompose.OutputBound

/-!
# One actual oracle call between two finite Boolean-stack programs

The input compiler and answer decoder are ordinary finite machines. A single
oracle transition replaces the compiled query by its answer; two destructive
reversal passes then transfer that answer to the decoder. No operation on an
unbounded word is supplied as a machine instruction.
-/

namespace Holant.Complexity.OracleOneQuery
open Turing Computability BinaryCompose

variable (a b : BinaryCompose.Machine)

abbrev Keys := BinaryCompose.Machine.Keys a b
abbrev States := BinaryCompose.Machine.States a b
abbrev Labels := a.Label ⊕ (b.Label ⊕ Option Bool)
abbrev Config := TM2.Cfg (fun _ : Keys a b => Bool) (Labels a b) (States a b)

def firstLabel (l : a.Label) : Labels a b := .inl l
def secondLabel (l : b.Label) : Labels a b := .inr (.inl l)
def queryLabel : Labels a b := .inr (.inr none)
def moveLabel : Labels a b := .inr (.inr (some false))
def restoreLabel : Labels a b := .inr (.inr (some true))

/-- Both programs are structurally embedded, with exactly one intervening query. -/
def program : Labels a b → OracleCommand (Keys a b) (Labels a b) (States a b)
  | .inl l => .ordinary (embedStmt (a.leftLayout b) (a.leftStates b)
      (firstLabel a b) (some (queryLabel a b)) (a.program l))
  | .inr (.inl l) => .ordinary (embedStmt (a.rightLayout b) (a.rightStates b)
      (secondLabel a b) none (b.program l))
  | .inr (.inr none) => .query (fun _ => moveLabel a b)
  | .inr (.inr (some false)) => .ordinary (StackProtocol.copyMoveStmt
      (a.sourceKey b) (a.temporaryKey b) (moveLabel a b) (restoreLabel a b))
  | .inr (.inr (some true)) => .ordinary (StackProtocol.copyMoveStmt
      (a.temporaryKey b) (a.destinationKey b) (restoreLabel a b) (secondLabel a b b.main))

abbrev machine : OracleMachine where
  K := Keys a b
  inputStack := .inl a.input
  outputStack := .inr (.inl b.output)
  queryStack := a.sourceKey b
  answerStack := a.sourceKey b
  Λ := Labels a b
  main := firstLabel a b a.main
  σ := States a b
  initialState := (none, a.initial, b.initial)
  program := program a b

def leftCfg (c : a.Config) : Config a b :=
  embedCfg (a.leftLayout b) (a.leftStates b) (firstLabel a b) (some (queryLabel a b)) c

def rightCfg (c : b.Config) : Config a b :=
  embedCfg (a.rightLayout b) (a.rightStates b) (secondLabel a b) none c

/-- Structural lifting works in an oracle machine at every ordinary source label. -/
theorem ordinary_step {m : BinaryCompose.Machine} {M : OracleMachine}
    (layout : StackEmbedding m.K M.K) (states : StateEmbedding m.State M.σ)
    (labels : m.Label → M.Λ) (stop : Option M.Λ)
    (agree : ∀ l, M.program (labels l) = .ordinary
      (embedStmt layout states labels stop (m.program l)))
    (oracle : List Bool → List Bool) (c d : m.Config)
    (h : m.computer.step c = some d) :
    M.step oracle (embedCfg layout states labels stop c) =
      some (embedCfg layout states labels stop d) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
    have hd : TM2.stepAux (m.program l) state tapes = d := Option.some.inj h
    subst d
    simp only [embedCfg, Option.elim_some, OracleMachine.step, agree, embed_stepAux]

/-- Timed executions are preserved transition for transition until the return. -/
theorem ordinary_run {m : BinaryCompose.Machine} {M : OracleMachine}
    (layout : StackEmbedding m.K M.K) (states : StateEmbedding m.State M.σ)
    (labels : m.Label → M.Λ) (stop : Option M.Λ)
    (agree : ∀ l, M.program (labels l) = .ordinary
      (embedStmt layout states labels stop (m.program l)))
    (oracle : List Bool → List Bool) (c d : m.Config) (n : ℕ)
    (h : (fun p => p.bind m.computer.step)^[n] (some c) = some d) :
    (fun p => p.bind (M.step oracle))^[n]
      (some (embedCfg layout states labels stop c)) =
      some (embedCfg layout states labels stop d) := by
  change (fun p => p.bind (TM2.step m.program))^[n] (some c) = some d at h
  induction n generalizing d with
  | zero => have hd := Option.some.inj h; subst d; rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (TM2.step m.program))^[n] (some c) with
    | none => simp [hp] at h
    | some prev =>
      have hs : TM2.step m.program prev = some d := by simpa only [hp, Option.bind_some] using h
      rw [Function.iterate_succ_apply', ih prev hp]
      exact ordinary_step layout states labels stop agree oracle prev d hs

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
      StackProtocol.cfg (queryLabel a b) (a.initial, b.initial)
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

/-- The only oracle call reads the actual compiled query and overwrites that tape. -/
theorem query_step (oracle : List Bool → List Bool) (query : List Bool) :
    (machine a b).step oracle (leftCfg a b (haltList a.computer query)) =
      some (StackProtocol.cfg (moveLabel a b) (a.initial, b.initial)
        (wordTape (a.sourceKey b) (oracle query))) := by
  rw [left_halt]
  simp [machine, OracleMachine.step, program, queryLabel, StackProtocol.cfg,
    wordTape]

/-- Answer copying preserves order and clears every temporary tape. -/
theorem transfer_run (oracle : List Bool → List Bool) (answer : List Bool) :
    (fun p => p.bind ((machine a b).step oracle))^[2 * (answer.length + 1)]
      (some (StackProtocol.cfg (moveLabel a b) (a.initial, b.initial)
        (wordTape (a.sourceKey b) answer))) =
      some (rightCfg a b (initList b.computer answer)) := by
  rw [right_init]
  exact transfer_exact ((machine a b).step oracle)
    (a.sourceKey b) (a.destinationKey b) (a.temporaryKey b)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (moveLabel a b) (restoreLabel a b) (secondLabel a b b.main)
    (by intro state tapes; rfl) (by intro state tapes; rfl)
    (a.initial, b.initial) answer

/-- Exact composed execution includes the real query and the answer transfer. -/
theorem run (oracle : List Bool → List Bool) (input query output : List Bool) (n m : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer query))
    (hb : (fun p => p.bind b.computer.step)^[m]
      (some (initList b.computer (oracle query))) = some (haltList b.computer output)) :
    (fun p => p.bind ((machine a b).step oracle))^[m + (2 * ((oracle query).length + 1) + (1 + n))]
      (some ((machine a b).init input)) = some ((machine a b).output output) := by
  have hfirst := ordinary_run (M := machine a b) (a.leftLayout b) (a.leftStates b) (firstLabel a b)
    (some (queryLabel a b)) (fun _ => rfl) oracle _ _ n ha
  have hlast := ordinary_run (M := machine a b) (a.rightLayout b) (a.rightStates b) (secondLabel a b)
    none (fun _ => rfl) oracle _ _ m hb
  change (fun p => p.bind ((machine a b).step oracle))^[n]
    (some (leftCfg a b _)) = some (leftCfg a b _) at hfirst
  change (fun p => p.bind ((machine a b).step oracle))^[m]
    (some (rightCfg a b _)) = some (rightCfg a b _) at hlast
  rw [left_init] at hfirst
  rw [right_halt] at hlast
  rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply,
    hfirst, Function.iterate_one, Option.bind_some, query_step, transfer_run]
  exact hlast

/-- A clean timed contract, with the actual answer length charged explicitly. -/
def outputs (oracle : List Bool → List Bool) (input query output : List Bool) (n m : ℕ)
    (ha : TM2OutputsInTime a.computer input (some query) n)
    (hb : TM2OutputsInTime b.computer (oracle query) (some output) m) :
    (machine a b).OutputsInTime oracle input output
      (n + 1 + 2 * ((oracle query).length + 1) + m) where
  steps := hb.steps + (2 * ((oracle query).length + 1) + (1 + ha.steps))
  evals_in_steps := run a b oracle input query output ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  steps_le_m := by have := ha.steps_le_m; have := hb.steps_le_m; omega

end Holant.Complexity.OracleOneQuery
