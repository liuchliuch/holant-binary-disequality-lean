import Holant.Complexity.MachineRename

/-! # Exact finite-state reorganization for oracle subroutines -/

namespace Holant.Complexity.OracleStateRename

open Turing

variable {τ : Type} [Fintype τ]

def command {K Λ σ : Type} (states : σ ≃ τ) : OracleCommand K Λ σ → OracleCommand K Λ τ
  | .ordinary q => .ordinary (MachineRename.stmt (Equiv.refl K) id states q)
  | .query next => .query (fun v => next (states.symm v))

abbrev machine (m : OracleMachine) (states : m.σ ≃ τ) : OracleMachine where
  K := m.K
  inputStack := m.inputStack
  outputStack := m.outputStack
  queryStack := m.queryStack
  answerStack := m.answerStack
  Λ := m.Λ
  main := m.main
  σ := τ
  initialState := states m.initialState
  program label := command states (m.program label)

def cfg (m : OracleMachine) (states : m.σ ≃ τ) (c : m.Cfg) : (machine m states).Cfg :=
  ⟨c.l, states c.var, c.stk⟩

theorem step (m : OracleMachine) (states : m.σ ≃ τ) (oracle : List Bool → List Bool) (c : m.Cfg) :
    (machine m states).step oracle (cfg m states c) = (m.step oracle c).map (cfg m states) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    cases hp : m.program label with
    | ordinary q =>
      have hh := MachineRename.stepAux_stmt (Equiv.refl m.K) id states q state tapes
      simpa [machine, OracleMachine.step, cfg, hp, command, MachineRename.cfg] using congrArg some hh
    | query next => simp [machine, OracleMachine.step, cfg, hp, command]

theorem run (m : OracleMachine) (states : m.σ ≃ τ) (oracle : List Bool → List Bool)
    (c : m.Cfg) (t : ℕ) :
    (fun p => p.bind ((machine m states).step oracle))^[t] (some (cfg m states c)) =
      ((fun p => p.bind (m.step oracle))^[t] (some c)).map (cfg m states) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    cases h : (fun p => p.bind (m.step oracle))^[t] (some c) with
    | none => rfl
    | some previous => exact step m states oracle previous

def liftTimed (m : OracleMachine) (states : m.σ ≃ τ) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (time : ℕ)
    (h : StateTransition.EvalsToInTime (m.step oracle) c (some d) time) :
    StateTransition.EvalsToInTime ((machine m states).step oracle) (cfg m states c)
      (some (cfg m states d)) time where
  steps := h.steps
  evals_in_steps := by
    change (fun p => p.bind ((machine m states).step oracle))^[h.steps] (some (cfg m states c)) = _
    rw [run]
    exact congrArg (Option.map (cfg m states)) h.evals_in_steps
  steps_le_m := h.steps_le_m

end Holant.Complexity.OracleStateRename
