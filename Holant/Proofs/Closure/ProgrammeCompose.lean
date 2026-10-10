import Holant.Proofs.Closure.ProgrammeComposeTrace
import Holant.Proofs.Closure.PhysicalTrace
import Holant.Proofs.Closure.TraceSupport

/-! Length control for genuine finite oracle-machine inlining. External query
validity is established from the complete actual composed transcript. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.Programme
open Holant.Complexity Computability Turing
open ProgrammeTraceRun

private theorem ordinaryStep_eq (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (label : m.Λ) (stmt : TM2.Stmt (fun _ : m.K => Bool) m.Λ m.σ)
    (hl : c.l = some label) (hp : m.program label = .ordinary stmt) :
    OracleBatch.ordinaryStep m c = m.step oracle c := by
  rcases c with ⟨l,v,s⟩
  change l = some label at hl
  subst l
  simp [OracleBatch.ordinaryStep, OracleMachine.step, hp]

private structure SafeWitness (callee caller : OracleMachine)
    (inner : List Bool → List Bool) (start : (OracleCompose.machine callee caller).Cfg)
    (source : caller.Cfg) (time : ℕ) (P : List Bool → Prop) where
  target : (OracleCompose.machine callee caller).Cfg
  related : OracleCompose.Related callee caller source target
  execution : TraceRun (OracleCompose.machine callee caller) inner start target time P

variable {α β γ δ ε ζ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
  {f : α → β} {g : γ → δ} {h : ε → ζ}

def queryPolynomial
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) : Polynomial ℕ :=
  r₂.queryBound.comp r₁.queryBound

private def QuerySafe (bound : Polynomial ℕ) (n : ℕ) (q : List Bool) : Prop :=
  ∃ y : ε, q = ee.encode y ∧ q.length ≤ bound.eval n

private theorem callee_words_safe
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (outer inner : List Bool → List Bool)
    (ho : RepresentsOracle ec ed g outer) (hi : RepresentsOracle ee ef h inner)
    (a : α) (t : ℕ) (c : r₁.reduction.machine.Cfg)
    (hr : r₁.reduction.machine.run outer (ea.encode a) t = some c)
    (hq : r₁.reduction.machine.IsQuery c)
    (value : List Bool) (time : ℕ)
    (hc : r₂.reduction.machine.OutputsInTime inner
      (c.stk r₁.reduction.machine.queryStack) value time) :
    ∀ q ∈ OracleBatch.queryTrace r₂.reduction.machine inner
      (r₂.reduction.machine.init (c.stk r₁.reduction.machine.queryStack)) hc.steps,
      QuerySafe (ee:=ee) (queryPolynomial r₁ r₂) (ea.encode a).length q := by
  obtain ⟨x, hx, hlen⟩ := r₁.safeQuery outer ho a t c hr hq
  intro q hqword
  obtain ⟨u, d, _hu, hrun, he, hquery⟩ := PhysicalTrace.queryTrace_member
    r₂.reduction.machine inner
      (r₂.reduction.machine.init (c.stk r₁.reduction.machine.queryStack)) hc.steps q hqword
  rw [hx] at hrun
  have hrun' : r₂.reduction.machine.run inner (ec.encode x) u = some d := hrun
  obtain ⟨y, hy, hbound⟩ := r₂.safeQuery inner hi x u d hrun' hquery
  refine ⟨y, he.trans hy, ?_⟩
  have hm := natPolynomial_eval_mono r₂.queryBound (show (ec.encode x).length ≤
      r₁.queryBound.eval (ea.encode a).length by simpa [hx] using hlen)
  rw [he]
  simpa only [queryPolynomial, Polynomial.eval_comp] using hbound.trans hm

private def simulate_step
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (outer inner : List Bool → List Bool)
    (ho : RepresentsOracle ec ed g outer) (hi : RepresentsOracle ee ef h inner)
    (a : α) (t : ℕ) (c c' : r₁.reduction.machine.Cfg)
    (d : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).Cfg)
    (ht : t ≤ r₁.reduction.time.eval (ea.encode a).length)
    (hr : r₁.reduction.machine.run outer (ea.encode a) t = some c)
    (hs : r₁.reduction.machine.step outer c = some c')
    (hd : OracleCompose.Related r₂.reduction.machine r₁.reduction.machine c d) :
    SafeWitness r₂.reduction.machine r₁.reduction.machine inner d c'
      ((r₁.compositionMacroPolynomial r₂.reduction).eval (ea.encode a).length)
      (QuerySafe (ee:=ee) (queryPolynomial r₁ r₂) (ea.encode a).length) := by
  let callee := r₂.reduction.machine
  let caller := r₁.reduction.machine
  let M := OracleCompose.machine callee caller
  let P := QuerySafe (ee:=ee) (queryPolynomial r₁ r₂) (ea.encode a).length
  let saved := Classical.choose hd
  have hsaved := Classical.choose_spec hd
  rw [hsaved]
  change caller.step outer c = some c' at hs
  rcases c with ⟨label,state,frame⟩
  cases label with
  | none => simp [OracleMachine.step] at hs
  | some label =>
    cases hp : caller.program label with
    | ordinary stmt =>
      have he : TM2.stepAux stmt state frame = c' := by
        simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
      subst c'
      have hstep := OracleCompose.ordinary_step callee caller inner label state frame saved stmt hp
      have hprog : M.program (.inr (.inr label)) = .ordinary (OracleCompose.stmt callee caller stmt) := by
        rw [OracleInline.program_outside]
        simp only [OracleCompose.outside, hp]
      have hordinary : OracleBatch.ordinaryStep M
          (OracleCompose.cfg callee caller ⟨some label,state,frame⟩ saved) =
          some (OracleCompose.cfg callee caller (TM2.stepAux stmt state frame) saved) := by
        rw [ordinaryStep_eq M inner _ (.inr (.inr label)) _ rfl hprog]
        exact hstep
      refine ⟨OracleCompose.cfg callee caller (TM2.stepAux stmt state frame) saved,
        ⟨saved,rfl⟩, ?_⟩
      exact (TraceRun.ordinary M inner _ _ 1 P
        (StackProtocol.runsExactly_one hordinary).toTimed).mono
          (r₁.compositionMacroPolynomial_pos r₂.reduction _)
    | query next =>
      have he : (⟨some (next state),state,
          Function.update frame caller.answerStack (outer (frame caller.queryStack))⟩ : caller.Cfg) = c' := by
        simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
      subst c'
      have hquery : caller.IsQuery ⟨some label,state,frame⟩ := ⟨label,next,rfl,hp⟩
      let certificate := r₁.compositionCallBound r₂.reduction outer inner ho hi a t
        ⟨some label,state,frame⟩ ht hr hquery
      have hsafe := callee_words_safe r₁ r₂ outer inner ho hi a t
        ⟨some label,state,frame⟩ hr hquery _ certificate.time certificate.evaluation
      have hlaunch := OracleCompose.query_launch callee caller inner label state frame saved next hp
      have hprog : M.program (.inr (.inr label)) = .ordinary
          (.load (fun v => (none, (callee.initialState, (v.2.2.1, next v.2.2.1))))
            (.goto (fun _ => OracleInline.phase callee caller.Λ 0))) := by
        rw [OracleInline.program_outside]
        simp only [OracleCompose.outside, hp]
        all_goals rfl
      have hordinary : OracleBatch.ordinaryStep M
          (OracleCompose.cfg callee caller ⟨some label,state,frame⟩ saved) =
          some (OracleInline.cfg callee (OracleInline.phase callee caller.Λ 0)
            (state,next state) (fun _ => []) frame) := by
        rw [ordinaryStep_eq M inner _ (.inr (.inr label)) _ rfl hprog]
        exact hlaunch
      let launch := TraceRun.ordinary M inner _ _ 1 P
        (StackProtocol.runsExactly_one hordinary).toTimed
      let callRaw := ProgrammeComposeTrace.call callee caller.queryStack caller.answerStack
        (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller)
        inner (state,next state) frame (outer (frame caller.queryStack)) certificate.time P
        certificate.evaluation hsafe
      let call := callRaw.withEntry (OracleInline.callerTape callee caller.inputStack)
        (OracleInline.callerTape callee caller.outputStack) (.inr (.inr caller.main))
      refine ⟨OracleCompose.cfg callee caller
          ⟨some (next state),state,Function.update frame caller.answerStack
            (outer (frame caller.queryStack))⟩ (next state), ⟨next state,rfl⟩, ?_⟩
      exact (launch.trans call).mono (by
        have hb := certificate.bound
        change certificate.time + 2 * (frame caller.queryStack).length +
          (frame caller.answerStack).length + 3 * (outer (frame caller.queryStack)).length + 9 ≤
            (r₁.compositionMacroPolynomial r₂.reduction).eval (ea.encode a).length at hb
        omega)

private def liftPrefix
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (outer inner : List Bool → List Bool)
    (ho : RepresentsOracle ec ed g outer) (hi : RepresentsOracle ee ef h inner)
    (a : α) (n : ℕ) (c : r₁.reduction.machine.Cfg)
    (hn : n ≤ r₁.reduction.time.eval (ea.encode a).length)
    (hr : r₁.reduction.machine.run outer (ea.encode a) n = some c) :
    SafeWitness r₂.reduction.machine r₁.reduction.machine inner
      ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).init (ea.encode a)) c
      (n * (r₁.compositionMacroPolynomial r₂.reduction).eval (ea.encode a).length)
      (QuerySafe (ee:=ee) (queryPolynomial r₁ r₂) (ea.encode a).length) := by
  let M := OracleCompose.machine r₂.reduction.machine r₁.reduction.machine
  let C := (r₁.compositionMacroPolynomial r₂.reduction).eval (ea.encode a).length
  let P := QuerySafe (ee:=ee) (queryPolynomial r₁ r₂) (ea.encode a).length
  induction n generalizing c with
  | zero =>
    have hc : r₁.reduction.machine.init (ea.encode a) = c := Option.some.inj hr
    subst c
    refine ⟨M.init (ea.encode a), ?_, ?_⟩
    · exact ⟨r₁.reduction.machine.main, (OracleCompose.cfg_init _ _ _).symm⟩
    · simpa only [Nat.zero_mul] using TraceRun.refl M inner (M.init (ea.encode a)) P
  | succ n ih =>
    rw [OracleMachine.run_succ] at hr
    cases hp : r₁.reduction.machine.run outer (ea.encode a) n with
    | none => simp [hp] at hr
    | some previous =>
      have hs : r₁.reduction.machine.step outer previous = some c := by simpa [hp] using hr
      let earlier := ih previous (by omega) hp
      let next := simulate_step r₁ r₂ outer inner ho hi a n previous c earlier.target
        (by omega) hp hs earlier.related
      refine ⟨next.target, next.related, ?_⟩
      exact (earlier.execution.trans next.execution).mono (by simp only [Nat.succ_mul]; omega)

private def composedTraceRun
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (inner : List Bool → List Bool) (hi : RepresentsOracle ee ef h inner) (a : α) :
    TraceRun (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine) inner
      ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).init (ea.encode a))
      ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).output (eb.encode (f a)))
      ((r₁.compositionTimePolynomial r₂.reduction).eval (ea.encode a).length)
      (QuerySafe (ee:=ee) (queryPolynomial r₁ r₂) (ea.encode a).length) := by
  let outer := encodedOracle ec ed g
  have ho := encodedOracle_represents ec ed g
  let callerRun := r₁.reduction.correct outer ho a
  let lifted := liftPrefix r₁ r₂ outer inner ho hi a callerRun.steps
    (r₁.reduction.machine.output (eb.encode (f a))) callerRun.steps_le_m callerRun.evals_in_steps
  have he : lifted.target =
      (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).output (eb.encode (f a)) := by
    obtain ⟨saved,hsaved⟩ := lifted.related
    rw [hsaved, OracleCompose.cfg_output]
  have actual := lifted.execution
  rw [he] at actual
  exact actual.mono (by
    simp only [LengthControlledOracleReduction.compositionTimePolynomial, Polynomial.eval_mul]
    exact Nat.mul_le_mul_right _ callerRun.steps_le_m)

/-- Genuine finite inlining of two controlled programmes. Query/answer copying,
old-answer clearing and returned output are already in the actual compiled clock. -/
def compose
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    LengthControlledOracleReduction ea eb ee ef f h where
  reduction := r₁.compose r₂.reduction
  targetOutput := r₂.targetOutput
  queryBound := queryPolynomial r₁ r₂
  safeQuery oracle ho a t c hr hq := by
    let actual := composedTraceRun r₁ r₂ oracle ho a
    have hmem := TraceSupport.reachable_query_mem_full_trace
      (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine) oracle
      (ea.encode a) (eb.encode (f a)) actual.steps t c actual.run hr hq
    exact actual.safe _ hmem

@[simp] theorem compose_machine
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    (compose r₁ r₂).reduction.machine =
      OracleCompose.machine r₂.reduction.machine r₁.reduction.machine := rfl

@[simp] theorem compose_time
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    (compose r₁ r₂).reduction.time = r₁.compositionTimePolynomial r₂.reduction := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.Programme
