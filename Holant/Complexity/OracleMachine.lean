import Holant.Complexity.Encoding

/-!
# Finite binary-stack machines with exact function-oracle calls

Ordinary instructions are mathlib TM2 statements over binary stacks and finite
control. The additional command replaces the answer stack by the exact oracle
answer to the query stack. Subsequent inspection and manipulation uses ordinary
stack instructions. Queries can depend on earlier answers.

One command costs one transition, including an oracle call. Since a fixed ordinary
statement is finite, its elementary stack-operation expansion has a fixed constant
factor. This module does not yet prove a simulation theorem, closure under reduction
composition, or a number-field arithmetic bit bound. In particular, for arbitrary
oracles with unbounded answer lengths, stack aliasing and unit-cost answers do not
yet constitute a proved compositional model of the paper's usual reductions.
Polynomial query/answer length bounds or a stricter protocol/simulation are required
before making that identification.
-/

namespace Holant.Complexity

open Computability Turing

/-- A program command is either a finite TM2 statement, or one oracle call followed
by a control label depending only on the finite internal state. -/
inductive OracleCommand (K Λ σ : Type) where
  | ordinary : TM2.Stmt (fun _ : K => Bool) Λ σ → OracleCommand K Λ σ
  | query : (σ → Λ) → OracleCommand K Λ σ

/-- Finite stacks, labels, internal control, and binary symbols on every stack. -/
structure OracleMachine where
  K : Type
  [decEqK : DecidableEq K]
  [finiteK : Fintype K]
  inputStack : K
  outputStack : K
  queryStack : K
  answerStack : K
  Λ : Type
  [finiteLabels : Fintype Λ]
  main : Λ
  σ : Type
  [finiteState : Fintype σ]
  initialState : σ
  program : Λ → OracleCommand K Λ σ

attribute [instance] OracleMachine.decEqK OracleMachine.finiteK
  OracleMachine.finiteLabels OracleMachine.finiteState

namespace OracleMachine

abbrev Cfg (m : OracleMachine) := TM2.Cfg (fun _ : m.K => Bool) m.Λ m.σ

/-- All stacks other than the input start empty. -/
def init (m : OracleMachine) (input : List Bool) : m.Cfg where
  l := some m.main
  var := m.initialState
  stk k := if k = m.inputStack then input else []

/-- At a successful clean halt, all stacks other than the output are empty and
finite internal memory has returned to its initial state. -/
def output (m : OracleMachine) (value : List Bool) : m.Cfg where
  l := none
  var := m.initialState
  stk k := if k = m.outputStack then value else []

/-- A query can read only the designated query stack; all non-oracle work is an
explicit TM2 statement. No arbitrary function on unbounded configurations occurs
in the program type. -/
def step (m : OracleMachine) (oracle : List Bool → List Bool) : m.Cfg → Option m.Cfg
  | ⟨none, _, _⟩ => none
  | ⟨some label, state, tapes⟩ =>
    match m.program label with
    | .ordinary stmt => some (TM2.stepAux stmt state tapes)
    | .query next => some ⟨some (next state), state,
        Function.update tapes m.answerStack (oracle (tapes m.queryStack))⟩

/-- Timed successful evaluation records an actual iterate of `step`. -/
abbrev OutputsInTime (m : OracleMachine) (oracle : List Bool → List Bool)
    (input value : List Bool) (time : ℕ) :=
  StateTransition.EvalsToInTime (m.step oracle) (m.init input) (some (m.output value)) time

@[simp] theorem step_output (m : OracleMachine) (oracle : List Bool → List Bool)
    (value : List Bool) : m.step oracle (m.output value) = none := rfl

end OracleMachine

/-- Correct encoded oracles agree on every valid encoded query. Behaviour on
malformed query strings is unspecified, and a reduction must work for every such
extension. This prevents extracting information from unspecified answers. -/
def RepresentsOracle {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)
    (f : α → β) (oracle : List Bool → List Bool) : Prop :=
  ∀ a, oracle (ea.encode a) = eb.encode (f a)

/-- Decoding supplies a total extension; invalid queries return the empty string.
Existence uses the supplied faithful decoder, without imposing a cost claim on it. -/
def encodedOracle {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)
    (f : α → β) (input : List Bool) : List Bool :=
  match ea.decode input with
  | some a => eb.encode (f a)
  | none => []

theorem encodedOracle_represents {α β : Type} (ea : Encoding α Bool)
    (eb : Encoding β Bool) (f : α → β) : RepresentsOracle ea eb f (encodedOracle ea eb f) := by
  intro a
  simp [encodedOracle]

/-- Polynomial-time function-oracle computation with explicit encodings and an
actual finite oracle program. The polynomial depends only on input length. -/
structure PolyTimeOracleReduction {α β γ δ : Type}
    (ea : Encoding α Bool) (eb : Encoding β Bool)
    (ec : Encoding γ Bool) (ed : Encoding δ Bool)
    (f : α → β) (g : γ → δ) where
  machine : OracleMachine
  time : Polynomial ℕ
  correct : ∀ oracle, RepresentsOracle ec ed g oracle → ∀ a,
    machine.OutputsInTime oracle (ea.encode a) (eb.encode (f a))
      (time.eval (ea.encode a).length)

/-- Existence of a reduction machine, rather than an uninterpreted hardness
predicate. Composition still requires a machine construction and proof. -/
def OracleReducible {α β γ δ : Type}
    (ea : Encoding α Bool) (eb : Encoding β Bool)
    (ec : Encoding γ Bool) (ed : Encoding δ Bool)
    (f : α → β) (g : γ → δ) : Prop :=
  Nonempty (PolyTimeOracleReduction ea eb ec ed f g)

/-- Reflexivity uses one query followed by one ordinary halt. A single stack is
simultaneously the input, query, answer, and output stack. -/
abbrev queryOnceMachine : OracleMachine where
  K := Unit
  inputStack := ()
  outputStack := ()
  queryStack := ()
  answerStack := ()
  Λ := Bool
  main := false
  σ := Unit
  initialState := ()
  program label := if label then .ordinary .halt else .query (fun _ => true)

/-- The two transitions really produce the oracle's exact answer. -/
def queryOnceMachine_outputs (oracle : List Bool → List Bool) (input : List Bool) :
    queryOnceMachine.OutputsInTime oracle input (oracle input) 2 where
  steps := 2
  evals_in_steps := by
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
      OracleMachine.init, OracleMachine.output, queryOnceMachine]
    congr 2
  steps_le_m := Nat.le_refl 2

/-- Encoded identity reduction in the exact-string oracle model defined here. -/
noncomputable def oracleReduction_refl {α β : Type} (ea : Encoding α Bool)
    (eb : Encoding β Bool) (f : α → β) : PolyTimeOracleReduction ea eb ea eb f f where
  machine := queryOnceMachine
  time := 2
  correct oracle h a := by
    have run := queryOnceMachine_outputs oracle (ea.encode a)
    rw [h a] at run
    simpa using run

theorem oracleReducible_refl {α β : Type} (ea : Encoding α Bool)
    (eb : Encoding β Bool) (f : α → β) : OracleReducible ea eb ea eb f f :=
  ⟨oracleReduction_refl ea eb f⟩

end Holant.Complexity
