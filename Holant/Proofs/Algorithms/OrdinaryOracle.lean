import Holant.Complexity.BinaryCompose.OutputBound
import Holant.Complexity.OracleReductionCompose


namespace Holant.LocalDrafts.MainChain.OrdinaryOracle
set_option backward.isDefEq.respectTransparency false

open Turing Computability Holant.Complexity Holant.Complexity.BinaryCompose

def AllOrdinary (m : OracleMachine) : Prop :=
  ∀ l, ∃ q, m.program l = .ordinary q

def lift (m : Machine) : OracleMachine where
  K := m.K
  inputStack := m.input
  outputStack := m.output
  queryStack := m.input
  answerStack := m.output
  Λ := m.Label
  main := m.main
  σ := m.State
  initialState := m.initial
  program l := .ordinary (m.program l)

theorem lift_ordinary (m : Machine) : AllOrdinary (lift m) := fun l => ⟨m.program l,rfl⟩

theorem lift_step (m : Machine) (oracle : List Bool → List Bool) :
    (lift m).step oracle = m.computer.step := by
  funext c
  rcases c with ⟨l,v,s⟩
  cases l <;> rfl

theorem lift_init (m : Machine) (input : List Bool) :
    (lift m).init input = initList m.computer input := by
  rw [m.init_eq]
  simp only [lift, OracleMachine.init, wordTape]
  congr 1
  funext k
  simp [Function.update] <;> rfl

theorem lift_output (m : Machine) (output : List Bool) :
    (lift m).output output = haltList m.computer output := by
  rw [m.halt_eq]
  simp only [lift, OracleMachine.output, wordTape]
  congr 1
  funext k
  simp [Function.update] <;> rfl

/-- No oracle is used: the correctness field is precisely the supplied
ordinary machine's already proved execution. -/
def liftReduction {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f : α → β} (a : Computes ea eb f) : PolyTimeOracleReduction ea eb ea eb f f where
  machine := lift a.machine
  time := a.time
  correct oracle _ x := by
    have h := a.outputs x
    exact {
      steps := h.steps
      steps_le_m := h.steps_le_m
      evals_in_steps := by simpa only [lift_step, lift_init, lift_output, Option.map_some] using h.evals_in_steps }

/-- Erasure is defined on every finite program. It is used only after proving
that the query case cannot occur at any label. -/
def erase (m : OracleMachine) : Machine where
  K := m.K
  input := m.inputStack
  output := m.outputStack
  Label := m.Λ
  main := m.main
  State := m.σ
  initial := m.initialState
  program l := match m.program l with
    | .ordinary q => q
    | .query _ => .halt

theorem erase_step (m : OracleMachine) (hm : AllOrdinary m)
    (oracle : List Bool → List Bool) : (erase m).computer.step = m.step oracle := by
  funext c
  rcases c with ⟨l,v,s⟩
  cases l with
  | none => rfl
  | some l =>
    obtain ⟨q,hq⟩ := hm l
    simp [erase, Machine.computer, FinTM2.step, TM2.step, OracleMachine.step, hq] <;> rfl

theorem erase_init (m : OracleMachine) (input : List Bool) :
    initList (erase m).computer input = m.init input := by
  rw [(erase m).init_eq]
  simp only [erase, OracleMachine.init, wordTape]
  congr 1
  funext k
  simp [Function.update] <;> rfl

theorem erase_output (m : OracleMachine) (output : List Bool) :
    haltList (erase m).computer output = m.output output := by
  rw [(erase m).halt_eq]
  simp only [erase, OracleMachine.output, wordTape]
  congr 1
  funext k
  simp [Function.update] <;> rfl

noncomputable def eraseReduction {α β γ δ : Type}
    {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}
    (r : PolyTimeOracleReduction ea eb ec ed f g) (hm : AllOrdinary r.machine) :
    Computes ea eb f where
  machine := erase r.machine
  time := r.time
  outputs x := by
    have h := r.correct (encodedOracle ec ed g) (encodedOracle_represents ec ed g) x
    exact {
      steps := h.steps
      steps_le_m := h.steps_le_m
      evals_in_steps := by
        simpa only [erase_step r.machine hm (encodedOracle ec ed g), erase_init, erase_output, Option.map_some] using h.evals_in_steps }

end Holant.LocalDrafts.MainChain.OrdinaryOracle
