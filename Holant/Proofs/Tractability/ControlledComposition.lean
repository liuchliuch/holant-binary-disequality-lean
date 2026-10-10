import Holant.Proofs.Platonic.PhysicalCostCompose

/-!
# Query control for the same finite oracle inliner

Technical replay of the already accepted physical protocol proof, preserving this module's original public API. The public composition consumes the same physical inliner
producer. The additional configuration provenance uses its ordinary protocol
receipts and its literal callee embedding; no second compiler is installed.
-/

namespace Holant.Complexity.ControlledComposition
open Holant.Complexity

open Turing StackProtocol

private inductive Trace {C : Type} (step : C → Option C) (P : C → Prop) :
    C → C → Prop
  | nil {a} : P a → Trace step P a a
  | cons {a b c} : P a → step a = some b → Trace step P b c → Trace step P a c

private theorem Trace.trans {C : Type} {step : C → Option C} {P : C → Prop}
    {a b c : C} (h : Trace step P a b) (h' : Trace step P b c) :
    Trace step P a c := by
  induction h generalizing c with
  | nil ha => exact h'
  | cons ha hs tail ih => exact .cons ha hs (ih (c := c) h')

private theorem Trace.one {C : Type} {step : C → Option C} {P : C → Prop}
    {a b : C} (ha : P a) (hs : step a = some b) (hb : P b) :
    Trace step P a b := .cons ha hs (.nil hb)

private theorem Trace.start {C : Type} {step : C → Option C} {P : C → Prop}
    {a b : C} (h : Trace step P a b) : P a := by
  cases h with
  | nil ha => exact ha
  | cons ha hs tail => exact ha

private theorem iterate_none {C : Type} (step : C → Option C) (n : ℕ) :
    (fun c => c.bind step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- A complete trace ending at the actual halt controls every prefix, including
the fact that no configuration survives a transition beyond that halt. -/
private theorem Trace.prefix {C : Type} {step : C → Option C} {P : C → Prop}
    {a b : C} (h : Trace step P a b) (hstop : step b = none)
    (t : ℕ) (c : C)
    (hr : (fun d => d.bind step)^[t] (some a) = some c) : P c := by
  revert hstop t c
  induction h with
  | @nil a ha =>
    intro hstop t c hr
    cases t with
    | zero => have he : a = c := Option.some.inj hr; subst c; exact ha
    | succ t =>
      rw [Function.iterate_succ_apply] at hr
      simp [hstop, iterate_none] at hr
  | @cons a b d ha hs tail ih =>
    intro hstop t c hr
    cases t with
    | zero => have he : a = c := Option.some.inj hr; subst c; exact ha
    | succ t =>
      rw [Function.iterate_succ_apply] at hr
      simp only [Option.bind_some, hs] at hr
      exact ih hstop t c hr

/-- Lift a real finite run, retaining the property at every intermediate source
configuration.  No arbitrary configuration-level opcode enters the program. -/
private theorem trace_embedded {C D : Type} (step : C → Option C)
    (target : D → Option D) (embed : C → D) (P : D → Prop)
    (start finish : C) (n : ℕ)
    (hr : (fun c => c.bind step)^[n] (some start) = some finish)
    (hs : ∀ c d, step c = some d → target (embed c) = some (embed d))
    (hp : ∀ t c, (fun d => d.bind step)^[t] (some start) = some c → P (embed c)) :
    Trace target P (embed start) (embed finish) := by
  induction n generalizing finish with
  | zero =>
    have he : start = finish := Option.some.inj hr
    subst finish
    exact .nil (hp 0 start rfl)
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hr
    cases hprev : (fun c => c.bind step)^[n] (some start) with
    | none => simp [hprev] at hr
    | some previous =>
      have hstep : step previous = some finish := by simpa only [hprev, Option.bind_some] using hr
      exact (ih previous hprev).trans
        (Trace.one (hp n previous hprev) (hs previous finish hstep)
          (hp (n + 1) finish (by rw [Function.iterate_succ_apply', hprev]; exact hstep)))

private theorem query_iff_words (m : OracleMachine) (c : m.Cfg) :
    m.IsQuery c ↔ OracleBatch.queryWords m c ≠ [] := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [OracleMachine.IsQuery, OracleBatch.queryWords]
  | some label =>
    cases hp : m.program label with
    | ordinary q => simp [OracleMachine.IsQuery, OracleBatch.queryWords, hp]
    | query next => simp [OracleMachine.IsQuery, OracleBatch.queryWords, hp]

private theorem caller_not_query (callee caller : OracleMachine) (c : caller.Cfg)
    (saved : caller.Λ) :
    ¬ (OracleCompose.machine callee caller).IsQuery (OracleCompose.cfg callee caller c saved) := by
  intro hq
  have hw := (query_iff_words _ _).mp hq
  exact hw (Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.caller_words_empty
    callee caller c saved)

/-- The literal left-label program preserves the original callee query command.
The returned phase-3 configuration is ordinary, even when the original callee
has already halted. -/
private theorem callee_isQuery_iff (callee caller : OracleMachine) (c : callee.Cfg)
    (memory : caller.σ × caller.Λ) (frame : caller.K → List Bool) :
    (OracleCompose.machine callee caller).IsQuery
      (OracleInline.calleeCfg callee c memory frame) ↔ callee.IsQuery c := by
  have words : OracleBatch.queryWords (OracleCompose.machine callee caller)
      (OracleInline.calleeCfg callee c memory frame) = OracleBatch.queryWords callee c := by
    simpa only [OracleCompose.machine, OracleCompose.base,
      Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.words_withEntry,
      Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.ordinary_withEntry,
      OracleMachine.step_withEntry] using
      Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.callee_words
        callee caller.queryStack caller.answerStack (caller.initialState, caller.main)
        Prod.snd (OracleCompose.outside callee caller) c memory frame
  rw [query_iff_words, words, ← query_iff_words]

/-- Successful ordinary execution has no query configuration except possibly
its final endpoint. This generic proof consumes old erased-step receipts; it
does not reconstruct any of the eight protocol loops. -/
private theorem ordinary_guard_trace (m : OracleMachine) (oracle : List Bool → List Bool)
    (P : m.Cfg → Prop) (hnq : ∀ c, ¬ m.IsQuery c → P c)
    (start finish : m.Cfg) (n : ℕ)
    (hr : (fun c => c.bind (OracleBatch.ordinaryStep m))^[n] (some start) = some finish)
    (hend : P finish) : Trace (m.step oracle) P start finish := by
  induction n generalizing start with
  | zero =>
    have he : start = finish := Option.some.inj hr
    subst start
    exact .nil hend
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hr
    cases hs : OracleBatch.ordinaryStep m start with
    | none => simp [hs] at hr
    | some next =>
      have ht : (fun c => c.bind (OracleBatch.ordinaryStep m))^[n] (some next) = some finish := by
        simpa only [Option.bind_some, hs] using hr
      have hnot : ¬ m.IsQuery start := by
        rintro ⟨label, continuation, hl, hp⟩
        rcases start with ⟨active, state, tapes⟩
        cases active with
        | none => cases hl
        | some active =>
          have he : active = label := Option.some.inj hl
          subst label
          simp [OracleBatch.ordinaryStep, hp] at hs
      exact .cons (hnq start hnot) (OracleBatch.ordinaryStep_spec m oracle start next hs).1
        (ih next ht)

end Holant.Complexity.ControlledComposition

namespace Holant.Complexity.LengthControlledOracleReduction
open Holant.Complexity

open Computability

variable {α β γ δ ε ζ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
  {f : α → β} {g : γ → δ} {h : ε → ζ}

/-- An external query in the actual compiled machine comes from a prefix of the
actual callee run on one valid query of the actual outer run.  The saved caller
frame is the original frame; query/answer stack aliasing is allowed. -/
def CompositionQueryOrigin
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (a : α)
    (c : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).Cfg) : Prop :=
  ∃ outerTime outerCfg q innerTime innerCfg memory,
    r₁.reduction.machine.run (encodedOracle ec ed g) (ea.encode a) outerTime = some outerCfg ∧
    r₁.reduction.machine.IsQuery outerCfg ∧
    outerCfg.stk r₁.reduction.machine.queryStack = ec.encode q ∧
    (ec.encode q).length ≤ r₁.queryBound.eval (ea.encode a).length ∧
    r₂.reduction.machine.run oracle (ec.encode q) innerTime = some innerCfg ∧
    r₂.reduction.machine.IsQuery innerCfg ∧
    c = OracleInline.calleeCfg r₂.reduction.machine innerCfg memory outerCfg.stk

end Holant.Complexity.LengthControlledOracleReduction

namespace Holant.Complexity.ControlledComposition
open Holant.Complexity

open Turing StackProtocol Computability LengthControlledOracleReduction

variable {α β γ δ ε ζ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
  {f : α → β} {g : γ → δ} {h : ε → ζ}

private def Guard (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (a : α)
    (c : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).Cfg) : Prop :=
  (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).IsQuery c →
    CompositionQueryOrigin r₁ r₂ oracle a c

private theorem prepare_trace (callee caller : OracleMachine)
    (oracle : List Bool → List Bool)
    (P : (OracleCompose.machine callee caller).Cfg → Prop)
    (hnq : ∀ c, ¬ (OracleCompose.machine callee caller).IsQuery c → P c)
    (memory : caller.σ × caller.Λ) (frame : caller.K → List Bool)
    (hentry : P (OracleInline.calleeCfg callee (callee.init (frame caller.queryStack)) memory frame)) :
    Trace ((OracleCompose.machine callee caller).step oracle) P
      (OracleInline.cfg callee (OracleInline.phase callee caller.Λ 0) memory (fun _ => []) frame)
      (OracleInline.calleeCfg callee (callee.init (frame caller.queryStack)) memory frame) := by
  let receipt := Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.prepare_ordinary
    callee caller.queryStack caller.answerStack (caller.initialState, caller.main)
    Prod.snd (OracleCompose.outside callee caller) memory frame
  apply ordinary_guard_trace (OracleCompose.machine callee caller) oracle P hnq _ _ receipt.steps _ hentry
  rw [show OracleBatch.ordinaryStep (OracleCompose.machine callee caller) =
      OracleBatch.ordinaryStep (OracleCompose.base callee caller) from
    Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.ordinary_withEntry _ _ _ _]
  exact receipt.evals_in_steps

private theorem finish_trace (callee caller : OracleMachine)
    (oracle : List Bool → List Bool)
    (P : (OracleCompose.machine callee caller).Cfg → Prop)
    (hnq : ∀ c, ¬ (OracleCompose.machine callee caller).IsQuery c → P c)
    (memory : caller.σ × caller.Λ) (frame : caller.K → List Bool) (value : List Bool)
    (hreturn : P (OracleInline.cfg callee (.inr (.inr memory.2)) memory
      (fun _ => []) (Function.update frame caller.answerStack value))) :
    Trace ((OracleCompose.machine callee caller).step oracle) P
      (OracleInline.calleeCfg callee (callee.output value) memory frame)
      (OracleInline.cfg callee (.inr (.inr memory.2)) memory (fun _ => [])
        (Function.update frame caller.answerStack value)) := by
  let receipt := Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.finish_ordinary
    callee caller.queryStack caller.answerStack (caller.initialState, caller.main)
    Prod.snd (OracleCompose.outside callee caller) memory frame value
  apply ordinary_guard_trace (OracleCompose.machine callee caller) oracle P hnq _ _ receipt.steps _ hreturn
  rw [show OracleBatch.ordinaryStep (OracleCompose.machine callee caller) =
      OracleBatch.ordinaryStep (OracleCompose.base callee caller) from
    Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.ordinary_withEntry _ _ _ _]
  exact receipt.evals_in_steps

private theorem call_trace
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (a : α) (outerTime : ℕ) (label : r₁.reduction.machine.Λ)
    (state : r₁.reduction.machine.σ) (frame : r₁.reduction.machine.K → List Bool)
    (saved : r₁.reduction.machine.Λ) (next : r₁.reduction.machine.σ → r₁.reduction.machine.Λ)
    (hp : r₁.reduction.machine.program label = .query next)
    (hr : r₁.reduction.machine.run (encodedOracle ec ed g) (ea.encode a) outerTime =
      some ⟨some label, state, frame⟩) :
    Trace ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).step oracle)
      (Guard r₁ r₂ oracle a)
      (OracleCompose.cfg r₂.reduction.machine r₁.reduction.machine ⟨some label, state, frame⟩ saved)
      (OracleCompose.cfg r₂.reduction.machine r₁.reduction.machine
        ⟨some (next state), state,
          Function.update frame r₁.reduction.machine.answerStack
            (encodedOracle ec ed g (frame r₁.reduction.machine.queryStack))⟩ (next state)) := by
  let callee := r₂.reduction.machine
  let caller := r₁.reduction.machine
  let memory := (state, next state)
  have hq : caller.IsQuery ⟨some label, state, frame⟩ := ⟨label, next, rfl, hp⟩
  obtain ⟨q, he, hlen⟩ := r₁.safeQuery (encodedOracle ec ed g)
    (encodedOracle_represents ec ed g) a outerTime _ hr hq
  change frame caller.queryStack = ec.encode q at he
  have hqLen : (ec.encode q).length ≤ r₁.queryBound.eval (ea.encode a).length := by
    change (frame caller.queryStack).length ≤ _ at hlen
    rwa [he] at hlen
  have hc : callee.OutputsInTime oracle (frame caller.queryStack)
      (encodedOracle ec ed g (frame caller.queryStack))
      (r₂.reduction.time.eval (ec.encode q).length) := by
    rw [he, encodedOracle_represents ec ed g q]
    exact r₂.reduction.correct oracle ho q
  have hcallee : ∀ t c,
      (fun d => d.bind (callee.step oracle))^[t] (some (callee.init (frame caller.queryStack))) = some c →
      Guard r₁ r₂ oracle a (OracleInline.calleeCfg callee c memory frame) := by
    intro t c hrun hquery
    have hi := (callee_isQuery_iff callee caller c memory frame).mp hquery
    refine ⟨outerTime, ⟨some label, state, frame⟩, q, t, c, memory,
      hr, hq, he, hqLen, ?_, hi, rfl⟩
    change (fun d => d.bind (callee.step oracle))^[t] (some (callee.init (ec.encode q))) = some c
    simpa only [he] using hrun
  have hnq : ∀ c, ¬ (OracleCompose.machine callee caller).IsQuery c → Guard r₁ r₂ oracle a c := by
    intro c hnot hquery
    exact False.elim (hnot hquery)
  have prepare := prepare_trace callee caller oracle (Guard r₁ r₂ oracle a) hnq memory frame
    (hcallee 0 (callee.init (frame caller.queryStack)) rfl)
  have launch : Trace ((OracleCompose.machine callee caller).step oracle) (Guard r₁ r₂ oracle a)
      (OracleCompose.cfg callee caller ⟨some label, state, frame⟩ saved)
      (OracleInline.cfg callee (OracleInline.phase callee caller.Λ 0) memory (fun _ => []) frame) := Trace.one
    (fun hquery => False.elim (caller_not_query callee caller _ saved hquery))
    (OracleCompose.query_launch callee caller oracle label state frame saved next hp)
    prepare.start
  have inner := trace_embedded (callee.step oracle)
    ((OracleCompose.machine callee caller).step oracle)
    (fun c => OracleInline.calleeCfg callee c memory frame) (Guard r₁ r₂ oracle a)
    (callee.init (frame caller.queryStack))
    (callee.output (encodedOracle ec ed g (frame caller.queryStack))) hc.steps hc.evals_in_steps
    (fun c d hs => by
      simpa only [OracleCompose.machine, OracleCompose.base,
      Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.words_withEntry,
      Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.ordinary_withEntry,
      OracleMachine.step_withEntry] using
        Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.callee_step
          callee caller.queryStack caller.answerStack (caller.initialState, caller.main)
          Prod.snd (OracleCompose.outside callee caller) oracle c d memory frame hs) hcallee
  have hreturn : Guard r₁ r₂ oracle a
      (OracleInline.cfg callee (.inr (.inr memory.2)) memory (fun _ => [])
        (Function.update frame caller.answerStack (encodedOracle ec ed g (frame caller.queryStack)))) := by
    change Guard r₁ r₂ oracle a (OracleCompose.cfg callee caller
      ⟨some (next state), state,
        Function.update frame caller.answerStack (encodedOracle ec ed g (frame caller.queryStack))⟩ (next state))
    intro hquery
    exact False.elim (caller_not_query callee caller _ (next state) hquery)
  have finish := finish_trace callee caller oracle (Guard r₁ r₂ oracle a) hnq memory frame
    (encodedOracle ec ed g (frame caller.queryStack)) hreturn
  exact ((launch.trans prepare).trans inner).trans finish

private theorem outer_trace
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (a : α) (n : ℕ) (finish : r₁.reduction.machine.Cfg)
    (hr : r₁.reduction.machine.run (encodedOracle ec ed g) (ea.encode a) n = some finish) :
    ∃ saved, Trace ((OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).step oracle)
      (Guard r₁ r₂ oracle a)
      (OracleCompose.cfg r₂.reduction.machine r₁.reduction.machine
        (r₁.reduction.machine.init (ea.encode a)) r₁.reduction.machine.main)
      (OracleCompose.cfg r₂.reduction.machine r₁.reduction.machine finish saved) := by
  induction n generalizing finish with
  | zero =>
    have he : r₁.reduction.machine.init (ea.encode a) = finish := Option.some.inj hr
    subst finish
    refine ⟨r₁.reduction.machine.main, .nil ?_⟩
    intro hquery
    exact False.elim (caller_not_query _ _ _ _ hquery)
  | succ n ih =>
    rw [OracleMachine.run_succ] at hr
    cases hprev : r₁.reduction.machine.run (encodedOracle ec ed g) (ea.encode a) n with
    | none => simp [hprev] at hr
    | some previous =>
      have hs : r₁.reduction.machine.step (encodedOracle ec ed g) previous = some finish := by
        simpa only [hprev, Option.bind_some] using hr
      obtain ⟨saved, trace⟩ := ih previous hprev
      rcases previous with ⟨label, state, frame⟩
      cases label with
      | none => simp [OracleMachine.step] at hs
      | some label =>
        cases hp : r₁.reduction.machine.program label with
        | ordinary q =>
          have he : TM2.stepAux q state frame = finish := by
            simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
          subst finish
          refine ⟨saved, trace.trans (Trace.one ?_ ?_ ?_)⟩
          · intro hquery; exact False.elim (caller_not_query _ _ _ saved hquery)
          · exact OracleCompose.ordinary_step _ _ oracle label state frame saved q hp
          · intro hquery; exact False.elim (caller_not_query _ _ _ saved hquery)
        | query next =>
          have he : (⟨some (next state), state,
              Function.update frame r₁.reduction.machine.answerStack
                (encodedOracle ec ed g (frame r₁.reduction.machine.queryStack))⟩ :
              r₁.reduction.machine.Cfg) = finish := by
            simpa only [OracleMachine.step, hp, Option.some.injEq] using hs
          subst finish
          exact ⟨next state, trace.trans
            (call_trace r₁ r₂ oracle ho a n label state frame saved next hp hprev)⟩

/-- Full successful outer execution supplies the actual finite prefix invariant;
callee correctness is used to finish each call, not to infer query safety. -/
theorem query_origin
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (a : α) (t : ℕ)
    (c : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).Cfg)
    (hr : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).run
      oracle (ea.encode a) t = some c)
    (hq : (OracleCompose.machine r₂.reduction.machine r₁.reduction.machine).IsQuery c) :
    CompositionQueryOrigin r₁ r₂ oracle a c := by
  have houter := r₁.reduction.correct (encodedOracle ec ed g) (encodedOracle_represents ec ed g) a
  obtain ⟨saved, trace⟩ := outer_trace r₁ r₂ oracle ho a houter.steps
    (r₁.reduction.machine.output (eb.encode (f a))) houter.evals_in_steps
  rw [OracleCompose.cfg_init, OracleCompose.cfg_output] at trace
  exact trace.prefix (OracleMachine.step_output _ oracle _) t c hr hq

end Holant.Complexity.ControlledComposition

namespace Holant.Complexity.LengthControlledOracleReduction
open Holant.Complexity

open Computability

variable {α β γ δ ε ζ : Type}
  {ea : Encoding α Bool} {eb : Encoding β Bool}
  {ec : Encoding γ Bool} {ed : Encoding δ Bool}
  {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
  {f : α → β} {g : γ → δ} {h : ε → ζ}

/-- The existing, fully charged inliner is closed under actual query control.
Both operands must be genuinely controlled reductions.  Target output control
is inherited from the second operand; source answer and stack control are then
produced by the existing `OracleSpace` theorems for this same reduction. -/
noncomputable def composeControlled
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    LengthControlledOracleReduction ea eb ee ef f h :=
  Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal.composeControlled r₁ r₂

/-- Public transport witness for every actual external-query prefix. -/
theorem composeControlled_query_origin
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (a : α) (t : ℕ) (c : (composeControlled r₁ r₂).reduction.machine.Cfg)
    (hr : (composeControlled r₁ r₂).reduction.machine.run oracle (ea.encode a) t = some c)
    (hq : (composeControlled r₁ r₂).reduction.machine.IsQuery c) :
    CompositionQueryOrigin r₁ r₂ oracle a c :=
  Holant.Complexity.ControlledComposition.query_origin r₁ r₂ oracle ho a t c hr hq

@[simp] theorem composeControlled_reduction
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    (composeControlled r₁ r₂).reduction = r₁.compose r₂.reduction := rfl

@[simp] theorem composeControlled_targetOutput
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    (composeControlled r₁ r₂).targetOutput = r₂.targetOutput := rfl

@[simp] theorem composeControlled_queryBound
    (r₁ : LengthControlledOracleReduction ea eb ec ed f g)
    (r₂ : LengthControlledOracleReduction ec ed ee ef g h) :
    (composeControlled r₁ r₂).queryBound = r₂.queryBound.comp r₁.queryBound := rfl

end Holant.Complexity.LengthControlledOracleReduction
