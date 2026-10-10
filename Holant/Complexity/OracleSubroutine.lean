import Holant.Complexity.MachineReturn
import Holant.Complexity.OracleMachine

/-!
# Operational embedding of a returning function-oracle subroutine

An actual finite binary-stack oracle machine can run inside a larger finite machine,
with extra caller stacks/memory preserved and control returning to a caller label.
Ordinary statements are structurally compiled; actual oracle calls keep their query
and answer stacks and oracle semantics. Exact transition counts are preserved up to
return. Top-level reduction composition still needs copy/clear orchestration.
-/

namespace Holant.Complexity.OracleSubroutine

open Turing

variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

/-- The compiled machine is explicitly finite in stacks, labels, memory, and symbols. -/
abbrev machine (m : OracleMachine) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (m.K ⊕ J) (m.Λ ⊕ R) (m.σ × τ)) : OracleMachine where
  K := m.K ⊕ J
  inputStack := .inl m.inputStack
  outputStack := .inl m.outputStack
  queryStack := .inl m.queryStack
  answerStack := .inl m.answerStack
  Λ := m.Λ ⊕ R
  main := .inl m.main
  σ := m.σ × τ
  initialState := (m.initialState, initialMemory)
  program label := match label with
    | .inl label => match m.program label with
      | .ordinary q => .ordinary (MachineReturn.stmt ret q)
      | .query next => .query (fun v => .inl (next v.1))
    | .inr label => outside label

/-- Every actual source transition, including an oracle-answer transition, is
reproduced while preserving the caller frame. -/
theorem step_of_step (m : OracleMachine) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (m.K ⊕ J) (m.Λ ⊕ R) (m.σ × τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (memory : τ) (frame : J → List Bool)
    (h : m.step oracle c = some d) :
    (machine m initialMemory ret outside).step oracle (MachineReturn.cfg ret c memory frame) =
      some (MachineReturn.cfg ret d memory frame) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => simp [OracleMachine.step] at h
  | some label =>
    cases hp : m.program label with
    | ordinary q =>
      have hd : TM2.stepAux q state tapes = d := by simpa [OracleMachine.step, hp] using h
      subst d
      simpa only [machine, OracleMachine.step, MachineReturn.cfg, Option.elim_some, hp] using
        congrArg some (MachineReturn.stepAux_stmt ret q state tapes memory frame)
    | query next =>
      have hd : (⟨some (next state), state,
        Function.update tapes m.answerStack (oracle (tapes m.queryStack))⟩ : m.Cfg) = d := by
        simpa [OracleMachine.step, hp] using h
      subst d
      simp only [machine, OracleMachine.step, MachineReturn.cfg, Option.elim_some, hp,
        Sum.elim_inl, MachineFrame.update_left]

/-- Finite actual executions lift through the oracle-subroutine compiler. -/
theorem run_program (m : OracleMachine) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (m.K ⊕ J) (m.Λ ⊕ R) (m.σ × τ))
    (oracle : List Bool → List Bool) (c : m.Cfg) (memory : τ) (frame : J → List Bool)
    (t : ℕ) (d : m.Cfg)
    (h : (fun p => p.bind (m.step oracle))^[t] (some c) = some d) :
    (fun p => p.bind ((machine m initialMemory ret outside).step oracle))^[t]
      (some (MachineReturn.cfg ret c memory frame)) = some (MachineReturn.cfg ret d memory frame) := by
  induction t generalizing d with
  | zero =>
    have hd : c = d := Option.some.inj h
    subst d
    rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply'] at h
    cases hp : (fun p => p.bind (m.step oracle))^[t] (some c) with
    | none => simp [hp] at h
    | some previous =>
      have hs : m.step oracle previous = some d := by simpa [hp] using h
      rw [Function.iterate_succ_apply', ih previous hp]
      exact step_of_step m initialMemory ret outside oracle previous d memory frame hs

/-- The original proved time bound is retained; oracle calls are neither skipped
nor replaced by arbitrary local computation. -/
def liftTimed (m : OracleMachine) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (m.K ⊕ J) (m.Λ ⊕ R) (m.σ × τ))
    (oracle : List Bool → List Bool) (c d : m.Cfg) (time : ℕ)
    (memory : τ) (frame : J → List Bool)
    (h : StateTransition.EvalsToInTime (m.step oracle) c (some d) time) :
    StateTransition.EvalsToInTime ((machine m initialMemory ret outside).step oracle)
      (MachineReturn.cfg ret c memory frame) (some (MachineReturn.cfg ret d memory frame)) time where
  steps := h.steps
  evals_in_steps := run_program m initialMemory ret outside oracle c memory frame h.steps d h.evals_in_steps
  steps_le_m := h.steps_le_m

end Holant.Complexity.OracleSubroutine
