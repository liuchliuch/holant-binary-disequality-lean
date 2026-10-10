import Holant.Complexity.OracleBatch.QueryCount

namespace Holant.Complexity.OracleBatch
open UniversalPairReduction.ThreeQuery

/-- The exact word presented by this active command, if it is an oracle call. -/
def queryWords (m : OracleMachine) (c : m.Cfg) : List (List Bool) :=
  match c.l with
  | none => []
  | some l => match m.program l with
    | .ordinary _ => []
    | .query _ => [c.stk m.queryStack]

/-- Ordered oracle transcript of actual transitions, including arbitrary prefixes. -/
def queryTrace (m : OracleMachine) (oracle : List Bool → List Bool) (c : m.Cfg) : ℕ → List (List Bool)
  | 0 => []
  | n+1 => match m.step oracle c with
    | none => []
    | some d => queryWords m c ++ queryTrace m oracle d n

theorem queryWords_length (m : OracleMachine) (c : m.Cfg) :
    (queryWords m c).length = queryCost m c := by
  rcases c with ⟨l,v,s⟩
  cases l with
  | none => rfl
  | some l => cases h : m.program l <;> simp [queryWords,queryCost,h]

theorem queryTrace_length (m : OracleMachine) (oracle : List Bool → List Bool) (c : m.Cfg) (n : ℕ) :
    (queryTrace m oracle c n).length = queryCount m oracle c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases h : m.step oracle c <;> simp [queryTrace,queryCount,h,queryWords_length,ih]

theorem queryTrace_add (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (n k : ℕ)
    (h : (fun p => p.bind (m.step oracle))^[n] (some c) = some d) :
    queryTrace m oracle c (n+k) = queryTrace m oracle c n ++ queryTrace m oracle d k := by
  induction n generalizing c with
  | zero => have hd := Option.some.inj h; subst d; simp [queryTrace]
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    cases hs : m.step oracle c with
    | none => simp [hs] at h
    | some e =>
      simp only [Option.bind_some,hs] at h
      simpa [Nat.succ_add,queryTrace,hs,List.append_assoc] using congrArg
        (fun x => queryWords m c ++ x) (ih e h)

/-- Execution and exact ordered query transcript, over the original transition
function. Lists occur only in this proof contract, never in finite control. -/
structure RunsTrace (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (n : ℕ) (qs : List (List Bool)) : Prop where
  run : (fun p => p.bind (m.step oracle))^[n] (some c) = some d
  trace : queryTrace m oracle c n = qs

theorem RunsTrace.trans {m : OracleMachine} {oracle : List Bool → List Bool}
    {c d e : m.Cfg} {n k : ℕ} {qs rs : List (List Bool)}
    (h : RunsTrace m oracle c d n qs) (h' : RunsTrace m oracle d e k rs) :
    RunsTrace m oracle c e (k+n) (qs ++ rs) := by
  refine ⟨?_,?_⟩
  · rw [Function.iterate_add_apply,h.run,h'.run]
  · rw [Nat.add_comm,queryTrace_add m oracle c d n k h.run,h.trace,h'.trace]

theorem RunsTrace.count {m : OracleMachine} {oracle : List Bool → List Bool}
    {c d : m.Cfg} {n : ℕ} {qs : List (List Bool)} (h : RunsTrace m oracle c d n qs) :
    queryCount m oracle c n = qs.length := by
  rw [← queryTrace_length,h.trace]

theorem ordinary_trace (m : OracleMachine) (oracle : List Bool → List Bool)
    (c d : m.Cfg) (n : ℕ)
    (h : (fun p => p.bind (ordinaryStep m))^[n] (some c) = some d) :
    RunsTrace m oracle c d n [] := by
  have hr := ordinary_run_count m oracle c d n h
  refine ⟨hr.1,?_⟩
  apply List.eq_nil_of_length_eq_zero
  rw [queryTrace_length,hr.2]

@[simp] theorem queryCount_output (m : OracleMachine) (oracle : List Bool → List Bool)
    (output : List Bool) (n : ℕ) : queryCount m oracle (m.output output) n = 0 := by
  cases n <;> rfl

theorem queryCount_mono (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (n k : ℕ) (h : n ≤ k) : queryCount m oracle c n ≤ queryCount m oracle c k := by
  induction k generalizing c n with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact Nat.le_refl _
  | succ k ih =>
    cases n with
    | zero => exact Nat.zero_le _
    | succ n =>
      cases hs : m.step oracle c with
      | none => simp [queryCount,hs]
      | some d =>
        simp only [queryCount,hs]
        exact Nat.add_le_add_left (ih d n (by omega)) _

/-- No prefix of a valid full execution, even one extending beyond its clean
halt, makes any additional hidden oracle calls. -/
theorem RunsTrace.prefix_count_le {m : OracleMachine} {oracle : List Bool → List Bool}
    {c : m.Cfg} {output : List Bool} {time : ℕ} {qs : List (List Bool)}
    (h : RunsTrace m oracle c (m.output output) time qs) (n : ℕ) :
    queryCount m oracle c n ≤ qs.length := by
  by_cases hn : n ≤ time
  · exact le_trans (queryCount_mono m oracle c n time hn) (le_of_eq h.count)
  · have hn' : time ≤ n := by omega
    have hc := queryCount_add m oracle c (m.output output) time (n-time) h.run
    rw [Nat.add_sub_of_le hn',queryCount_output,Nat.add_zero,h.count] at hc
    exact le_of_eq hc

end Holant.Complexity.OracleBatch
