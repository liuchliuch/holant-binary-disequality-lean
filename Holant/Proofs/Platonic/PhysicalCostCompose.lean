import Holant.Proofs.Platonic.PhysicalCostProtocol

/-! Ported proof; verification is recorded in the task build logs. Query provenance for the EXISTING composition machine.
The proof lifts complete actual caller prefixes together with the exact
callee transcripts. prepare/finish/launch have empty external transcripts.
The public inliner and its original time polynomial are kept verbatim.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal
open Computability Holant.Complexity Turing OracleBatch
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false


/-- Entry metadata changes neither real steps nor external query words. -/
@[simp] theorem words_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ)
    (c : m.Cfg) : queryWords (m.withEntry input output main) c = queryWords m c := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label => cases hp : m.program label <;> simp [queryWords,OracleMachine.withEntry,hp]

@[simp] theorem ordinary_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ) :
    ordinaryStep (m.withEntry input output main) = ordinaryStep m := by
  funext c
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label => cases hp : m.program label <;> simp [ordinaryStep,OracleMachine.withEntry,hp]

@[simp] theorem trace_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ)
    (oracle : List Bool → List Bool) (c : m.Cfg) (n : ℕ) :
    queryTrace (m.withEntry input output main) oracle c n = queryTrace m oracle c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hs : m.step oracle c <;>
      simp only [queryTrace,OracleMachine.step_withEntry,hs,words_withEntry,ih]

@[simp] theorem runsTrace_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ)
    (oracle : List Bool → List Bool) (c d : m.Cfg) (n : ℕ) (words : List (List Bool)) :
    RunsTrace (m.withEntry input output main) oracle c d n words ↔ RunsTrace m oracle c d n words := by
  constructor <;> intro h
  · exact ⟨by simpa only [OracleMachine.step_withEntry] using h.run,
      by simpa only [trace_withEntry] using h.trace⟩
  · exact ⟨by simpa only [OracleMachine.step_withEntry] using h.run,
      by simpa only [trace_withEntry] using h.trace⟩

/-- Converse direction for the actual trace: each recorded word came
from a reachable query configuration before the given transition count. -/
theorem trace_member_query (m : OracleMachine) (oracle : List Bool → List Bool)
    (start : m.Cfg) (n : ℕ) (word : List Bool)
    (hm : word ∈ queryTrace m oracle start n) :
    ∃ t c, t < n ∧ (fun p => p.bind (m.step oracle))^[t] (some start) = some c ∧
      m.IsQuery c ∧ word = c.stk m.queryStack := by
  induction n generalizing start with
  | zero => simp [queryTrace] at hm
  | succ n ih =>
      cases hs : m.step oracle start with
      | none => simp [queryTrace,hs] at hm
      | some next =>
          rw [queryTrace,hs,List.mem_append] at hm
          rcases hm with first | later
          · rcases start with ⟨label,state,tapes⟩
            cases label with
            | none => simp [queryWords] at first
            | some label =>
                cases hp : m.program label with
                | ordinary stmt => simp [queryWords,hp] at first
                | query nextLabel =>
                    have hw : word = tapes m.queryStack := by simpa [queryWords,hp] using first
                    exact ⟨0,⟨some label,state,tapes⟩,Nat.zero_lt_succ n,rfl,
                      ⟨label,nextLabel,rfl,hp⟩,hw⟩
          · obtain ⟨t,c,ht,hr,hq,hw⟩ := ih next later
            refine ⟨t+1,c,Nat.succ_lt_succ ht,?_,hq,hw⟩
            simpa only [Function.iterate_succ_apply,Option.bind_some,hs] using hr

theorem caller_words_empty (callee caller : OracleMachine) (c : caller.Cfg) (saved : caller.Λ) :
    queryWords (OracleCompose.machine callee caller) (OracleCompose.cfg callee caller c saved) = [] := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label =>
      have hp := OracleInline.program_outside callee caller.queryStack caller.answerStack
        (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller) label
      cases hc : caller.program label <;>
        simp only [queryWords,OracleCompose.machine,OracleCompose.base,OracleMachine.withEntry,OracleCompose.cfg,
          OracleInline.machine,OracleInline.rawMachine,OracleStateRename.machine,
          OracleSubroutine.machine,OracleStateRename.command,
          Option.map_some,OracleCompose.outside,hc]

/-- Exact existing macro: ordinary launch, old prepare, actual callee
trace, old finish. No caller/temporary command leaks an external query. -/
theorem query_macro_trace (callee caller : OracleMachine) (oracle : List Bool → List Bool)
    (label : caller.Λ) (state : caller.σ) (frame : caller.K → List Bool) (saved : caller.Λ)
    (next : caller.σ → caller.Λ) (hp : caller.program label = .query next)
    (value : List Bool) (time : ℕ)
    (h : callee.OutputsInTime oracle (frame caller.queryStack) value time) :
    ∃ n, RunsTrace (OracleCompose.machine callee caller) oracle
      (OracleCompose.cfg callee caller ⟨some label,state,frame⟩ saved)
      (OracleCompose.cfg callee caller
        ⟨some (next state),state,Function.update frame caller.answerStack value⟩ (next state))
      n (queryTrace callee oracle (callee.init (frame caller.queryStack)) h.steps) := by
  let M := OracleCompose.machine callee caller
  have launch := OracleCompose.query_launch callee caller oracle label state frame saved next hp
  have first : RunsTrace M oracle
      (OracleCompose.cfg callee caller ⟨some label,state,frame⟩ saved)
      (OracleInline.cfg callee (OracleInline.phase callee caller.Λ 0)
        (state,next state) (fun _ => []) frame) 1 [] := by
    constructor
    · exact (StackProtocol.runsExactly_one launch)
    · simp only [M,queryTrace,launch,caller_words_empty,List.nil_append]
  let prepare := prepare_ordinary callee caller.queryStack caller.answerStack
    (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller)
    (state,next state) frame
  have preparation : RunsTrace M oracle
      (OracleInline.cfg callee (OracleInline.phase callee caller.Λ 0)
        (state,next state) (fun _ => []) frame)
      (OracleInline.calleeCfg callee (callee.init (frame caller.queryStack)) (state,next state) frame)
      prepare.steps [] := by
    simpa only [M,OracleCompose.machine,OracleCompose.base,runsTrace_withEntry] using
      ordinary_trace (OracleInline.machine callee caller.queryStack caller.answerStack
        (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller))
        oracle _ _ prepare.steps prepare.evals_in_steps
  have inner : RunsTrace M oracle
      (OracleInline.calleeCfg callee (callee.init (frame caller.queryStack)) (state,next state) frame)
      (OracleInline.calleeCfg callee (callee.output value) (state,next state) frame) h.steps
      (queryTrace callee oracle (callee.init (frame caller.queryStack)) h.steps) := by
    simpa only [M,OracleCompose.machine,OracleCompose.base,runsTrace_withEntry] using
      callee_trace callee caller.queryStack caller.answerStack
        (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller)
        oracle _ _ (state,next state) frame h.steps h.evals_in_steps
  let finish := finish_ordinary callee caller.queryStack caller.answerStack
    (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller)
    (state,next state) frame value
  have finishing : RunsTrace M oracle
      (OracleInline.calleeCfg callee (callee.output value) (state,next state) frame)
      (OracleCompose.cfg callee caller
        ⟨some (next state),state,Function.update frame caller.answerStack value⟩ (next state))
      finish.steps [] := by
    simpa only [M,OracleCompose.machine,OracleCompose.base,runsTrace_withEntry,OracleCompose.cfg,OracleInline.cfg,
      Option.map_some,Option.elim_some] using
      ordinary_trace (OracleInline.machine callee caller.queryStack caller.answerStack
        (caller.initialState,caller.main) Prod.snd (OracleCompose.outside callee caller))
        oracle _ _ finish.steps finish.evals_in_steps
  refine ⟨finish.steps+(h.steps+(prepare.steps+1)),?_⟩
  simpa only [List.nil_append,List.append_nil] using ((first.trans preparation).trans inner).trans finishing

variable {α β γ δ ε ζ : Type}
variable {ea : Encoding α Bool} {eb : Encoding β Bool}
variable {ec : Encoding γ Bool} {ed : Encoding δ Bool}
variable {ee : Encoding ε Bool} {ef : Encoding ζ Bool}
variable {f : α → β} {g : γ → δ} {h : ε → ζ}
variable (first : LengthControlledOracleReduction ea eb ec ed f g)
variable (last : LengthControlledOracleReduction ec ed ee ef g h)

def queryPolynomial : Polynomial ℕ := last.queryBound.comp first.queryBound
def WordsControlled (x : α) (words : List (List Bool)) : Prop :=
  ∀ word ∈ words, ∃ q : ε, word = ee.encode q ∧ word.length ≤ (queryPolynomial first last).eval (ea.encode x).length

/-- Data in this witness are the actual target execution and transcript,
not a desired endpoint/contract. The caller relation is the old cfg relation. -/
structure TraceWitness (oracle : List Bool → List Bool) (x : α)
    (start : (OracleCompose.machine last.reduction.machine first.reduction.machine).Cfg)
    (source : first.reduction.machine.Cfg) : Type where
  target : (OracleCompose.machine last.reduction.machine first.reduction.machine).Cfg
  related : OracleCompose.Related last.reduction.machine first.reduction.machine source target
  steps : ℕ
  words : List (List Bool)
  execution : RunsTrace (OracleCompose.machine last.reduction.machine first.reduction.machine)
    oracle start target steps words
  controlled : WordsControlled first last x words

/-- One actually reachable caller command has a controlled real macro.
Only the existing first safeQuery and last safeQuery producers are used. -/
def step_trace (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (x : α) (t : ℕ) (c c' : first.reduction.machine.Cfg)
    (d : (OracleCompose.machine last.reduction.machine first.reduction.machine).Cfg)
    (hr : first.reduction.machine.run (encodedOracle ec ed g) (ea.encode x) t = some c)
    (hs : first.reduction.machine.step (encodedOracle ec ed g) c = some c')
    (hd : OracleCompose.Related last.reduction.machine first.reduction.machine c d) :
    TraceWitness first last oracle x d c' := by
  classical
  apply Classical.choice
  obtain ⟨saved,rfl⟩ := hd
  rcases c with ⟨label,state,frame⟩
  cases label with
  | none => simp [OracleMachine.step] at hs
  | some label =>
      cases hp : first.reduction.machine.program label with
      | ordinary stmt =>
          have hc' : TM2.stepAux stmt state frame = c' := by
            simpa only [OracleMachine.step,hp,Option.some.injEq] using hs
          subst c'
          let target := OracleCompose.cfg last.reduction.machine first.reduction.machine
            (TM2.stepAux stmt state frame) saved
          have step := OracleCompose.ordinary_step last.reduction.machine first.reduction.machine
            oracle label state frame saved stmt hp
          refine ⟨⟨target,⟨saved,rfl⟩,1,[],?_,?_⟩⟩
          · constructor
            · exact StackProtocol.runsExactly_one step
            · simp only [queryTrace,step,caller_words_empty,List.nil_append]
          · intro word hm
            simp at hm
      | query next =>
          have hq : first.reduction.machine.IsQuery ⟨some label,state,frame⟩ :=
            ⟨label,next,rfl,hp⟩
          obtain ⟨q,he,hlen⟩ := first.safeQuery (encodedOracle ec ed g)
            (encodedOracle_represents ec ed g) x t _ hr hq
          change frame first.reduction.machine.queryStack = ec.encode q at he
          have value_eq : encodedOracle ec ed g (frame first.reduction.machine.queryStack) =
              ed.encode (g q) := by rw [he]; exact encodedOracle_represents ec ed g q
          have hc' : (⟨some (next state),state,Function.update frame first.reduction.machine.answerStack
              (ed.encode (g q))⟩ : first.reduction.machine.Cfg) = c' := by
            simpa only [OracleMachine.step,hp,value_eq,Option.some.injEq] using hs
          subst c'
          let inner := last.reduction.correct oracle ho q
          have run : last.reduction.machine.OutputsInTime oracle
              (frame first.reduction.machine.queryStack) (ed.encode (g q))
              (last.reduction.time.eval (ec.encode q).length) := by
            rw [he]
            exact inner
          obtain ⟨n,trace⟩ := query_macro_trace last.reduction.machine first.reduction.machine
            oracle label state frame saved next hp (ed.encode (g q)) _ run
          refine ⟨⟨_,⟨next state,rfl⟩,n,_,trace,?_⟩⟩
          intro word hm
          obtain ⟨u,ci,_,hc,hqi,hw⟩ := trace_member_query last.reduction.machine oracle
            (last.reduction.machine.init (frame first.reduction.machine.queryStack)) run.steps word hm
          have reach : last.reduction.machine.run oracle (ec.encode q) u = some ci := by
            simpa only [OracleMachine.run,he] using hc
          obtain ⟨original,hword,hbound⟩ := last.safeQuery oracle ho q u ci reach hqi
          refine ⟨original,hw.trans hword,?_⟩
          have qlength : (ec.encode q).length ≤ first.queryBound.eval (ea.encode x).length := by
            simpa only [he] using hlen
          have bound := hbound.trans (natPolynomial_eval_mono last.queryBound qlength)
          simpa only [queryPolynomial,Polynomial.eval_comp,hw] using bound

/-- Induct on the ACTUAL successful caller prefix. Macro traces are joined
in order; no assumed whole-interpreter query receipt is a premise. -/
def prefix_trace (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (x : α) (n : ℕ) (c : first.reduction.machine.Cfg)
    (hr : first.reduction.machine.run (encodedOracle ec ed g) (ea.encode x) n = some c) :
    TraceWitness first last oracle x
      ((OracleCompose.machine last.reduction.machine first.reduction.machine).init (ea.encode x)) c := by
  induction n generalizing c with
  | zero =>
      have hc : first.reduction.machine.init (ea.encode x) = c := Option.some.inj hr
      subst c
      refine ⟨_,⟨first.reduction.machine.main,(OracleCompose.cfg_init _ _ _).symm⟩,0,[],⟨rfl,rfl⟩,?_⟩
      intro word hm
      simp at hm
  | succ n ih =>
      rw [OracleMachine.run_succ] at hr
      cases hp : first.reduction.machine.run (encodedOracle ec ed g) (ea.encode x) n with
      | none => simp [hp] at hr
      | some previous =>
          have hs : first.reduction.machine.step (encodedOracle ec ed g) previous = some c := by
            simpa only [hp,Option.bind_some] using hr
          let before := ih previous hp
          let next := step_trace first last oracle ho x n previous c before.target hp hs before.related
          refine ⟨next.target,next.related,next.steps+before.steps,before.words++next.words,
            before.execution.trans next.execution,?_⟩
          intro word hm
          rcases List.mem_append.mp hm with hm | hm
          · exact before.controlled word hm
          · exact next.controlled word hm

theorem composed_complete_trace (oracle : List Bool → List Bool)
    (ho : RepresentsOracle ee ef h oracle) (x : α) :
    ∃ n words, RunsTrace (OracleCompose.machine last.reduction.machine first.reduction.machine) oracle
      ((OracleCompose.machine last.reduction.machine first.reduction.machine).init (ea.encode x))
      ((OracleCompose.machine last.reduction.machine first.reduction.machine).output (eb.encode (f x)))
      n words ∧ WordsControlled first last x words := by
  let old := first.reduction.correct (encodedOracle ec ed g) (encodedOracle_represents ec ed g) x
  let run := prefix_trace first last oracle ho x old.steps (first.reduction.machine.output (eb.encode (f x)))
    old.evals_in_steps
  obtain ⟨saved,same⟩ := run.related
  have endpoint : run.target = (OracleCompose.machine last.reduction.machine first.reduction.machine).output
      (eb.encode (f x)) := same.trans (OracleCompose.cfg_output _ _ _ saved)
  refine ⟨run.steps,run.words,?_,run.controlled⟩
  exact endpoint ▸ run.execution

/-- Length control of EXACTLY the old inlined machine/time/correct proof.
No arbitrary Poly machine is upgraded: both actual constituent certificates
are used operationally to produce its complete transcript above. -/
def composeControlled : LengthControlledOracleReduction ea eb ee ef f h where
  reduction := first.compose last.reduction
  targetOutput := last.targetOutput
  queryBound := queryPolynomial first last
  safeQuery oracle ho x t c hr hq := by
    obtain ⟨n,words,trace,control⟩ := composed_complete_trace first last oracle ho x
    have hm := TraceQueryControl.transcript_member trace t c hr hq
    obtain ⟨q,hword,hlen⟩ := control _ hm
    exact ⟨q,hword,hlen⟩

theorem composeControlled_reduction : (composeControlled first last).reduction = first.compose last.reduction := rfl
theorem composeControlled_queryBound : (composeControlled first last).queryBound =
    last.queryBound.comp first.queryBound := rfl

/-- Abstract dependent transport to the identical delivered reduction. This
does not unfold the actual finite catalogue when its Cfg type is compared. -/
theorem reduction_safeQuery
    (control : LengthControlledOracleReduction ea eb ee ef f h)
    (old : PolyTimeOracleReduction ea eb ee ef f h) (same : control.reduction = old)
    (oracle : List Bool → List Bool) (ho : RepresentsOracle ee ef h oracle)
    (x : α) (t : ℕ) (c : old.machine.Cfg)
    (hr : old.machine.run oracle (ea.encode x) t = some c) (hq : old.machine.IsQuery c) :
    ∃ q, c.stk old.machine.queryStack = ee.encode q ∧
      (c.stk old.machine.queryStack).length ≤ control.queryBound.eval (ea.encode x).length := by
  cases same
  exact control.safeQuery oracle ho x t c hr hq

end Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.Internal
