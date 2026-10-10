import Holant.Complexity.OracleInlineCost
import Holant.Complexity.OracleMetadata
import Holant.Complexity.TimedSimulation

/-!
# Finite caller compilation for oracle inlining

Every ordinary caller statement is compiled structurally. Each caller query jumps
through the proved copy/call/clear protocol; only the callee can make an external
oracle call. All control, scratch memory, labels and stack collections are finite.
-/

namespace Holant.Complexity.OracleCompose

open Turing

abbrev Tape (callee caller : OracleMachine) := OracleInline.Tape callee caller.K
abbrev Label (callee caller : OracleMachine) := OracleInline.Label callee caller.Λ
abbrev State (callee caller : OracleMachine) := OracleInline.State callee (caller.σ × caller.Λ)

/-- Source halt also resets the saved return label to the fixed initial value. -/
def stmt (callee caller : OracleMachine) :
    TM2.Stmt (fun _ : caller.K => Bool) caller.Λ caller.σ →
      TM2.Stmt (fun _ : Tape callee caller => Bool) (Label callee caller) (State callee caller)
  | .push k f q => .push (OracleInline.callerTape callee k) (fun v => f v.2.2.1) (stmt callee caller q)
  | .pop k f q => .pop (OracleInline.callerTape callee k)
      (fun v bit => (v.1, (v.2.1, (f v.2.2.1 bit, v.2.2.2)))) (stmt callee caller q)
  | .peek k f q => .peek (OracleInline.callerTape callee k)
      (fun v bit => (v.1, (v.2.1, (f v.2.2.1 bit, v.2.2.2)))) (stmt callee caller q)
  | .load f q => .load (fun v => (v.1, (v.2.1, (f v.2.2.1, v.2.2.2)))) (stmt callee caller q)
  | .branch f a b => .branch (fun v => f v.2.2.1) (stmt callee caller a) (stmt callee caller b)
  | .goto f => .goto (fun v => .inr (.inr (f v.2.2.1)))
  | .halt => .load (fun v => (none, (callee.initialState, (v.2.2.1, caller.main)))) .halt

/-- Resetting the saved return label adds at most one primitive instruction. -/
theorem budget_stmt_le (callee caller : OracleMachine)
    (q : TM2.Stmt (fun _ : caller.K => Bool) caller.Λ caller.σ) :
    TM2Cost.budget (stmt callee caller q) ≤ TM2Cost.budget q + 1 := by
  induction q <;> simp only [stmt, TM2Cost.budget] at * <;> omega

/-- Every pending saved return label is finite; it is irrelevant between calls. -/
def cfg (callee caller : OracleMachine) (c : caller.Cfg) (saved : caller.Λ) :
    TM2.Cfg (fun _ : Tape callee caller => Bool) (Label callee caller) (State callee caller) where
  l := c.l.map (fun l => .inr (.inr l))
  var := (none, (callee.initialState, (c.var, c.l.elim caller.main (fun _ => saved))))
  stk := OracleInline.tapes callee (fun _ => []) c.stk

/-- Compiled ordinary statements preserve the actual caller words and finite state. -/
theorem stepAux_stmt (callee caller : OracleMachine)
    (q : TM2.Stmt (fun _ : caller.K => Bool) caller.Λ caller.σ)
    (state : caller.σ) (frame : caller.K → List Bool) (saved : caller.Λ) :
    TM2.stepAux (stmt callee caller q) (none, (callee.initialState, (state, saved)))
      (OracleInline.tapes callee (fun _ => []) frame) =
      cfg callee caller (TM2.stepAux q state frame) saved := by
  induction q generalizing state frame with
  | push k f q ih =>
    simpa only [stmt, TM2.stepAux, OracleInline.tapes_caller, OracleInline.update_caller] using
      ih state (Function.update frame k (f state :: frame k))
  | pop k f q ih =>
    simpa only [stmt, TM2.stepAux, OracleInline.tapes_caller, OracleInline.update_caller] using
      ih (f state (frame k).head?) (Function.update frame k (frame k).tail)
  | peek k f q ih =>
    simpa only [stmt, TM2.stepAux, OracleInline.tapes_caller, OracleInline.update_caller] using ih (f state (frame k).head?) frame
  | load f q ih => simpa only [stmt, TM2.stepAux] using ih (f state) frame
  | branch f a b ha hb => cases h : f state <;> simp [stmt, TM2.stepAux, h, ha, hb]
  | goto f => rfl
  | halt => rfl

/-- A caller query records its continuation and enters the finite protocol. -/
def outside (callee caller : OracleMachine) (label : caller.Λ) :
    OracleCommand (Tape callee caller) (Label callee caller) (State callee caller) :=
  match caller.program label with
  | .ordinary q => .ordinary (stmt callee caller q)
  | .query next => .ordinary (.load (fun v => (none, (callee.initialState, (v.2.2.1, next v.2.2.1))))
      (.goto (fun _ => OracleInline.phase callee caller.Λ 0)))

abbrev base (callee caller : OracleMachine) : OracleMachine :=
  OracleInline.machine callee caller.queryStack caller.answerStack (caller.initialState, caller.main)
    Prod.snd (outside callee caller)

/-- The compiled program starts in the actual caller and uses its input/output stacks. -/
abbrev machine (callee caller : OracleMachine) : OracleMachine :=
  (base callee caller).withEntry (OracleInline.callerTape callee caller.inputStack)
    (OracleInline.callerTape callee caller.outputStack) (.inr (.inr caller.main))

@[simp] theorem step_machine (callee caller : OracleMachine) (oracle : List Bool → List Bool) :
    (machine callee caller).step oracle = (base callee caller).step oracle :=
  OracleMachine.step_withEntry _ _ _ _ _

/-- The caller's ordinary command executes in one real compiled transition. -/
theorem ordinary_step (callee caller : OracleMachine) (oracle : List Bool → List Bool)
    (label : caller.Λ) (state : caller.σ) (frame : caller.K → List Bool) (saved : caller.Λ)
    (q : TM2.Stmt (fun _ : caller.K => Bool) caller.Λ caller.σ)
    (h : caller.program label = .ordinary q) :
    (machine callee caller).step oracle (cfg callee caller ⟨some label, state, frame⟩ saved) =
      some (cfg callee caller (TM2.stepAux q state frame) saved) := by
  rw [step_machine]
  change (base callee caller).step oracle
    ⟨some (.inr (.inr label)), (none, (callee.initialState, (state, saved))),
      OracleInline.tapes callee (fun _ => []) frame⟩ = _
  have hp : (base callee caller).program (.inr (.inr label)) = .ordinary (stmt callee caller q) := by
    rw [OracleInline.program_outside]
    simp only [outside, h]
  rw [OracleMachine.step, hp]
  exact congrArg some (stepAux_stmt callee caller q state frame saved)

/-- One launch transition saves the actual caller continuation. -/
theorem query_launch (callee caller : OracleMachine) (oracle : List Bool → List Bool)
    (label : caller.Λ) (state : caller.σ) (frame : caller.K → List Bool) (saved : caller.Λ)
    (next : caller.σ → caller.Λ) (h : caller.program label = .query next) :
    (machine callee caller).step oracle (cfg callee caller ⟨some label, state, frame⟩ saved) =
      some (OracleInline.cfg callee (OracleInline.phase callee caller.Λ 0)
        (state, next state) (fun _ => []) frame) := by
  rw [step_machine]
  have hp : (base callee caller).program (.inr (.inr label)) =
      .ordinary (.load (fun v => (none, (callee.initialState, (v.2.2.1, next v.2.2.1))))
        (.goto (fun _ => OracleInline.phase callee caller.Λ 0))) := by
    rw [OracleInline.program_outside]
    simp only [outside, h]
  change (base callee caller).step oracle
    ⟨some (.inr (.inr label)), (none, (callee.initialState, (state, saved))),
      OracleInline.tapes callee (fun _ => []) frame⟩ = _
  rw [OracleMachine.step, hp]
  rfl

/-- One caller query is replaced by launch plus the full bit-charged call protocol. -/
def query_correct (callee caller : OracleMachine) (oracle : List Bool → List Bool)
    (label : caller.Λ) (state : caller.σ) (frame : caller.K → List Bool) (saved : caller.Λ)
    (next : caller.σ → caller.Λ) (h : caller.program label = .query next)
    (value : List Bool) (time : ℕ)
    (hc : callee.OutputsInTime oracle (frame caller.queryStack) value time) :
    StateTransition.EvalsToInTime ((machine callee caller).step oracle)
      (cfg callee caller ⟨some label, state, frame⟩ saved)
      (some (cfg callee caller ⟨some (next state), state, Function.update frame caller.answerStack value⟩ (next state)))
      (time + 2 * (frame caller.queryStack).length + (frame caller.answerStack).length + 3 * value.length + 9) := by
  have hlaunch := (StackProtocol.runsExactly_one (query_launch callee caller oracle label state frame saved next h)).toTimed
  have hcall := OracleInline.call_correct callee caller.queryStack caller.answerStack
    (caller.initialState, caller.main) Prod.snd (outside callee caller) oracle (state, next state) frame value time hc
  rw [← step_machine] at hcall
  have joined := StateTransition.EvalsToInTime.trans ((machine callee caller).step oracle) 1
    (time + 2 * (frame caller.queryStack).length + (frame caller.answerStack).length + 3 * value.length + 8)
    _ _ _ hlaunch hcall
  convert joined using 1
  rfl

theorem cfg_init (callee caller : OracleMachine) (input : List Bool) :
    cfg callee caller (caller.init input) caller.main = (machine callee caller).init input := by
  simp only [cfg, OracleMachine.init, Option.map_some, Option.elim_some]
  congr 1
  funext k
  rcases k with k | k
  · simp [OracleInline.tapes, OracleInline.callerTape]
  · rcases k with k | k
    · simp [OracleInline.tapes, OracleInline.callerTape]
    · simp [OracleInline.tapes, OracleInline.callerTape]

theorem cfg_output (callee caller : OracleMachine) (output : List Bool) (saved : caller.Λ) :
    cfg callee caller (caller.output output) saved = (machine callee caller).output output := by
  simp only [cfg, OracleMachine.output, Option.map_none, Option.elim_none]
  congr 1
  funext k
  rcases k with k | k
  · simp [OracleInline.tapes, OracleInline.callerTape]
  · rcases k with k | k
    · simp [OracleInline.tapes, OracleInline.callerTape]
    · simp [OracleInline.tapes, OracleInline.callerTape]

/-- A per-query certificate includes the callee execution and every protocol cost. -/
structure CallBound (callee caller : OracleMachine) (inner outer : List Bool → List Bool)
    (c : caller.Cfg) (C : ℕ) where
  time : ℕ
  evaluation : callee.OutputsInTime inner (c.stk caller.queryStack)
    (outer (c.stk caller.queryStack)) time
  bound : time + 2 * (c.stk caller.queryStack).length + (c.stk caller.answerStack).length +
    3 * (outer (c.stk caller.queryStack)).length + 9 ≤ C

/-- The finite saved return label is the only irrelevant part of an embedded caller. -/
def Related (callee caller : OracleMachine) (c : caller.Cfg) (d : (machine callee caller).Cfg) : Prop :=
  ∃ saved, d = cfg callee caller c saved

/-- Any actual source transition has its proved finite target macro. -/
noncomputable def simulate_step (callee caller : OracleMachine)
    (outer inner : List Bool → List Bool) (C : ℕ) (hC : 1 ≤ C)
    (c c' : caller.Cfg) (d : (machine callee caller).Cfg)
    (hs : caller.step outer c = some c') (hd : Related callee caller c d)
    (hc : caller.IsQuery c → CallBound callee caller inner outer c C) :
    TimedSimulation.Witness ((machine callee caller).step inner) (Related callee caller) d c' C := by
  classical
  let saved := Classical.choose hd
  have hsaved := Classical.choose_spec hd
  rw [hsaved]
  rcases c with ⟨label, state, frame⟩
  cases label with
  | none => simp [OracleMachine.step] at hs
  | some label =>
    cases hp : caller.program label with
    | ordinary q =>
      have he : TM2.stepAux q state frame = c' := by simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
      subst c'
      refine ⟨cfg callee caller (TM2.stepAux q state frame) saved, ⟨saved, rfl⟩, ?_⟩
      have hrun := (StackProtocol.runsExactly_one
        (ordinary_step callee caller inner label state frame saved q hp)).toTimed
      exact ⟨hrun.toEvalsTo, le_trans hrun.steps_le_m hC⟩
    | query next =>
      have he : (⟨some (next state), state,
          Function.update frame caller.answerStack (outer (frame caller.queryStack))⟩ : caller.Cfg) = c' := by
        simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
      subst c'
      let certificate := hc ⟨label, next, rfl, hp⟩
      refine ⟨cfg callee caller _ (next state), ⟨next state, rfl⟩, ?_⟩
      let hrun := query_correct callee caller inner label state frame saved next hp
        (outer (frame caller.queryStack)) certificate.time certificate.evaluation
      exact ⟨hrun.toEvalsTo, le_trans hrun.steps_le_m certificate.bound⟩

/-- All actual caller transitions compose into the concrete finite inlined program.
The query certificates need only hold along the given source execution. -/
noncomputable def outputs (callee caller : OracleMachine) (outer inner : List Bool → List Bool)
    (input output : List Bool) (time C : ℕ) (h : caller.OutputsInTime outer input output time)
    (hC : 1 ≤ C)
    (calls : ∀ t c, t < time → caller.run outer input t = some c → caller.IsQuery c →
      CallBound callee caller inner outer c C) :
    (machine callee caller).OutputsInTime inner input output (time * C) := by
  let run := TimedSimulation.liftTimed (caller.step outer) ((machine callee caller).step inner)
    (Related callee caller) (caller.init input) ((machine callee caller).init input)
    ⟨caller.main, (cfg_init callee caller input).symm⟩ time C
    (fun t ht c c' d hr hs hd => simulate_step callee caller outer inner C hC c c' d hs hd
      (calls t c ht hr)) (caller.output output) h
  have he : run.target = (machine callee caller).output output := by
    obtain ⟨saved, hs⟩ := run.related
    rw [hs, cfg_output]
  have evaluation := run.evaluation
  rw [he] at evaluation
  exact evaluation

end Holant.Complexity.OracleCompose
