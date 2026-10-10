import Holant.Complexity.OracleBatch.QueryTrace
import Holant.Complexity.OracleQueryBounds

/-! Reconstructed exact ordered-query support. Every word is related to an
actual reachable query configuration; repeated equal words remain distinct
transcript occurrences. No oracle validity is assumed by these trace lemmas. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.PhysicalTrace
open Holant.Complexity Computability

/-- A recorded word is precisely the active query stack of this configuration. -/
theorem queryWords_member (m : OracleMachine) (c : m.Cfg) (q : List Bool)
    (hq : q ∈ OracleBatch.queryWords m c) :
    q = c.stk m.queryStack ∧ m.IsQuery c := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => simp [OracleBatch.queryWords] at hq
  | some label =>
    cases hp : m.program label with
    | ordinary stmt => simp [OracleBatch.queryWords,hp] at hq
    | query next =>
      have he : q = tapes m.queryStack := by simpa [OracleBatch.queryWords,hp] using hq
      exact ⟨he,label,next,rfl,hp⟩

/-- Ordered transcript membership gives a genuine earlier iterate and query,
including the exact presented stack word and its strict prefix position. -/
theorem queryTrace_member (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (t : ℕ) (q : List Bool)
    (hq : q ∈ OracleBatch.queryTrace m oracle c t) :
    ∃ (u : ℕ) (d : m.Cfg), u < t ∧
      (fun p => p.bind (m.step oracle))^[u] (some c) = some d ∧
      q = d.stk m.queryStack ∧ m.IsQuery d := by
  induction t generalizing c with
  | zero => simp [OracleBatch.queryTrace] at hq
  | succ t ih =>
    cases hs : m.step oracle c with
    | none => simp [OracleBatch.queryTrace,hs] at hq
    | some next =>
      simp only [OracleBatch.queryTrace,hs,List.mem_append] at hq
      rcases hq with here | later
      · have hh := queryWords_member m c q here
        exact ⟨0,c,by omega,rfl,hh.1,hh.2⟩
      · obtain ⟨u,d,hu,hr,he,hquery⟩ := ih next later
        refine ⟨u+1,d,by omega,?_,he,hquery⟩
        rw [Function.iterate_succ_apply]
        simpa only [Option.bind_some,hs] using hr

theorem queryWords_length_le (m : OracleMachine) (c : m.Cfg) :
    (OracleBatch.queryWords m c).length ≤ 1 := by
  rcases c with ⟨label,state,tapes⟩
  cases label with
  | none => simp [OracleBatch.queryWords]
  | some label => cases hp : m.program label <;> simp [OracleBatch.queryWords,hp]

/-- An actual step contributes at most one word, even with repeated queries. -/
theorem queryTrace_length_le (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (t : ℕ) : (OracleBatch.queryTrace m oracle c t).length ≤ t := by
  induction t generalizing c with
  | zero => simp [OracleBatch.queryTrace]
  | succ t ih =>
    cases hs : m.step oracle c with
    | none => simp [OracleBatch.queryTrace,hs]
    | some next =>
      simp only [OracleBatch.queryTrace,hs,List.length_append]
      have hw := queryWords_length_le m c
      have ht := ih next
      omega

/-- Query and answer lengths are charged once for each occurrence in the LIST,
not once for each distinct value or set membership witness. -/
theorem transcript_sum_le (oracle : List Bool → List Bool) (qs : List (List Bool))
    (Q A : ℕ) (bounds : ∀ q ∈ qs, q.length ≤ Q ∧ (oracle q).length ≤ A) :
    (qs.map List.length).sum + (qs.map (fun q => (oracle q).length)).sum ≤
      qs.length * (Q+A) := by
  revert bounds
  induction qs with
  | nil => intro h; simp
  | cons q qs ih =>
    intro bounds
    have head := bounds q (by simp)
    have tail := ih (by
      intro w hw
      exact bounds w (List.mem_cons_of_mem q hw))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

end Holant.LocalDrafts.RemoteWork.StableClosureV2.PhysicalTrace
