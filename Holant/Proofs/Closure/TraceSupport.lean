import Holant.Complexity.OracleBatch.QueryTrace
import Holant.Complexity.OracleQueryBounds

/-! Exact actual-query membership in a completed oracle-machine transcript.
Recovered proof reconstruction: no query-safety or termination oracle is added.
The full concrete run to output is the same existing machine run. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.TraceSupport
open Holant.Complexity

theorem trace_mono (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (n k : ℕ) (hle : n ≤ k) :
    (OracleBatch.queryTrace m oracle c n).Sublist (OracleBatch.queryTrace m oracle c k) := by
  induction k generalizing c n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact List.Sublist.refl _
  | succ k ih =>
      cases n with
      | zero => simp [OracleBatch.queryTrace]
      | succ n =>
          cases hs : m.step oracle c with
          | none => simp [OracleBatch.queryTrace,hs]
          | some d =>
              simp only [OracleBatch.queryTrace,hs]
              exact (List.Sublist.refl _).append (ih d n (by omega))

theorem active_query_member (m : OracleMachine) (oracle : List Bool → List Bool)
    (input : List Bool) (t : ℕ) (c : m.Cfg)
    (run : m.run oracle input t = some c) (query : m.IsQuery c) :
    c.stk m.queryStack ∈ OracleBatch.queryTrace m oracle (m.init input) (t+1) := by
  rw [OracleBatch.queryTrace_add m oracle (m.init input) c t 1 run]
  apply List.mem_append.mpr
  right
  obtain ⟨label,next,hl,hp⟩ := query
  rcases c with ⟨l,v,s⟩
  change l = some label at hl
  subst l
  simp [OracleBatch.queryTrace,OracleBatch.queryWords,OracleMachine.step,hp]

@[simp] theorem trace_output (m : OracleMachine) (oracle : List Bool → List Bool)
    (output : List Bool) (n : ℕ) :
    OracleBatch.queryTrace m oracle (m.output output) n = [] := by
  cases n <;> rfl

/-- Every actual finite prefix, including a bound beyond the clean halt,
has no query word absent from the actual complete transcript. -/
theorem prefix_sublist_full (m : OracleMachine) (oracle : List Bool → List Bool)
    (input output : List Bool) (T n : ℕ)
    (full : m.run oracle input T = some (m.output output)) :
    (OracleBatch.queryTrace m oracle (m.init input) n).Sublist
      (OracleBatch.queryTrace m oracle (m.init input) T) := by
  by_cases hn : n ≤ T
  · exact trace_mono m oracle (m.init input) n T hn
  · have hT : T ≤ n := by omega
    have h := OracleBatch.queryTrace_add m oracle (m.init input) (m.output output)
      T (n-T) full
    rw [Nat.add_sub_of_le hT,trace_output,List.append_nil] at h
    rw [h]

/-- The exact public boundary consumed by the physical composition compiler.
No bound on the supplied reachable-query time is assumed. -/
theorem reachable_query_mem_full_trace (m : OracleMachine) (oracle : List Bool → List Bool)
    (input output : List Bool) (T t : ℕ) (c : m.Cfg)
    (full : m.run oracle input T = some (m.output output))
    (hprefix : m.run oracle input t = some c) (query : m.IsQuery c) :
    c.stk m.queryStack ∈ OracleBatch.queryTrace m oracle (m.init input) T :=
  (prefix_sublist_full m oracle input output T (t+1) full).subset
    (active_query_member m oracle input t c hprefix query)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.TraceSupport
