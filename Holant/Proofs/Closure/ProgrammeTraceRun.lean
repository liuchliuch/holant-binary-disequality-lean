import Holant.Proofs.Closure.ProgrammeProtocol
import Holant.Proofs.Closure.ProgrammeCalleeTrace
import Holant.Complexity.OracleMetadata
import Holant.Complexity.OracleReductionCompose

/-! Reconstructed proof contract for a real finite execution and its SAME
ordered query transcript. Natural step counts are data; bounds and query safety
are proved for those exact steps. No hidden computation is a machine command. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeTraceRun
open Holant.Complexity Computability

structure TraceRun (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (time : ℕ) (P : List Bool → Prop) where
  steps : ℕ
  bound : steps ≤ time
  run : (fun p => p.bind (m.step oracle))^[steps] (some c) = some d
  safe : ∀ q ∈ OracleBatch.queryTrace m oracle c steps, P q

namespace TraceRun
variable {m : OracleMachine} {oracle : List Bool → List Bool}
variable {c d e : m.Cfg} {n k : ℕ} {P : List Bool → Prop}

def refl (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (P : List Bool → Prop) : TraceRun m oracle c c 0 P where
  steps := 0
  bound := Nat.le_refl _
  run := rfl
  safe := by intro q hq; simp [OracleBatch.queryTrace] at hq

def mono (h : TraceRun m oracle c d n P) (hnk : n ≤ k) : TraceRun m oracle c d k P where
  steps := h.steps
  bound := h.bound.trans hnk
  run := h.run
  safe := h.safe

/-- Actual concatenation adds real step counts and ordered transcript lists. -/
def trans (h : TraceRun m oracle c d n P) (h' : TraceRun m oracle d e k P) :
    TraceRun m oracle c e (n+k) P where
  steps := h'.steps+h.steps
  bound := by have hn := h.bound; have hk := h'.bound; omega
  run := by rw [Function.iterate_add_apply,h.run,h'.run]
  safe := by
    intro q hq
    rw [Nat.add_comm,OracleBatch.queryTrace_add m oracle c d h.steps h'.steps h.run] at hq
    rcases List.mem_append.mp hq with before | after
    · exact h.safe q before
    · exact h'.safe q after

/-- Frozen ordinary-run erasure proves this segment has no actual queries. -/
def ordinary (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (time : ℕ) (P : List Bool → Prop)
    (h : StateTransition.EvalsToInTime (OracleBatch.ordinaryStep m) c (some d) time) :
    TraceRun m oracle c d time P := by
  let tr := OracleBatch.ordinary_trace m oracle c d h.steps h.evals_in_steps
  refine ⟨h.steps,h.steps_le_m,tr.run,?_⟩
  intro q hq
  rw [tr.trace] at hq
  simp at hq

def toTimed (h : TraceRun m oracle c d n P) :
    StateTransition.EvalsToInTime (m.step oracle) c (some d) n where
  steps := h.steps
  evals_in_steps := h.run
  steps_le_m := h.bound

end TraceRun

/-- Entry metadata preserves the actual active query word. -/
theorem queryWords_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ)
    (c : m.Cfg) : OracleBatch.queryWords (m.withEntry input output main) c =
      OracleBatch.queryWords m c := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some label =>
    cases hp : m.program label <;>
      simp [OracleBatch.queryWords,OracleMachine.withEntry,hp]

/-- Entry metadata changes no actual transitions, queries or transcript word. -/
theorem queryTrace_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ)
    (oracle : List Bool → List Bool) (c : m.Cfg) (t : ℕ) :
    OracleBatch.queryTrace (m.withEntry input output main) oracle c t =
      OracleBatch.queryTrace m oracle c t := by
  induction t generalizing c with
  | zero => rfl
  | succ t ih =>
    simp only [OracleBatch.queryTrace,OracleMachine.step_withEntry]
    cases hs : m.step oracle c with
    | none => rfl
    | some next =>
      simp only [hs]
      rw [ih,queryWords_withEntry]

namespace TraceRun
variable {m : OracleMachine} {oracle : List Bool → List Bool}
variable {c d : m.Cfg} {time : ℕ} {P : List Bool → Prop}

def withEntry (h : TraceRun m oracle c d time P)
    (input output : m.K) (main : m.Λ) :
    TraceRun (m.withEntry input output main) oracle c d time P where
  steps := h.steps
  bound := h.bound
  run := by simpa only [OracleMachine.step_withEntry] using h.run
  safe := by
    intro q hq
    rw [queryTrace_withEntry] at hq
    exact h.safe q hq

end TraceRun
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ProgrammeTraceRun
