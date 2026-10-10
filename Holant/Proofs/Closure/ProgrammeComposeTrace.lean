import Holant.Proofs.Closure.ProgrammeTraceRun

/-! Query safety of the actual finite caller compiler, derived from its launch,
copy, callee and restoration executions. No external-query backend is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeComposeTrace
open Holant.Complexity Turing StackProtocol
open Holant.Complexity.OracleInline
open ProgrammeTraceRun

variable {J R τ : Type} [DecidableEq J] [Fintype J] [Fintype R] [Fintype τ]

def call (m : OracleMachine) (query answer : J) (initialMemory : τ) (ret : τ → R)
    (outside : R → OracleCommand (Tape m J) (Label m R) (State m τ))
    (oracle : List Bool → List Bool) (memory : τ) (frame : J → List Bool)
    (value : List Bool) (time : ℕ) (P : List Bool → Prop)
    (h : m.OutputsInTime oracle (frame query) value time)
    (hsafe : ∀ q ∈ OracleBatch.queryTrace m oracle (m.init (frame query)) h.steps, P q) :
    TraceRun (machine m query answer initialMemory ret outside) oracle
      (OracleInline.cfg m (phase m R 0) memory (fun _ => []) frame)
      (OracleInline.cfg m (.inr (.inr (ret memory))) memory (fun _ => [])
        (Function.update frame answer value))
      (time + 2 * (frame query).length + (frame answer).length + 3 * value.length + 8) P := by
  let M := machine m query answer initialMemory ret outside
  let hp := ProgrammeProtocol.prepare_ordinary m query answer initialMemory ret outside
    oracle memory frame
  let hf := ProgrammeProtocol.finish_ordinary m query answer initialMemory ret outside
    oracle memory frame value
  let prep := TraceRun.ordinary M oracle _ _ _ P hp
  let finish := TraceRun.ordinary M oracle _ _ _ P hf
  let inner : TraceRun M oracle
      (calleeCfg m (m.init (frame query)) memory frame)
      (calleeCfg m (m.output value) memory frame) time P :=
    { steps := h.steps
      bound := h.steps_le_m
      run := ProgrammeCalleeTrace.callee_run m query answer initialMemory ret outside oracle
        (m.init (frame query)) (m.output value) memory frame h.steps h.evals_in_steps
      safe := fun q hq => hsafe q (by
        rw [ProgrammeCalleeTrace.callee_trace m query answer initialMemory ret outside oracle
          (m.init (frame query)) (m.output value) memory frame h.steps h.evals_in_steps] at hq
        exact hq) }
  exact ((prep.trans inner).trans finish).mono (by omega)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeComposeTrace
