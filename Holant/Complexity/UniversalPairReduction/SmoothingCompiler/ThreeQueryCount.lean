import Holant.Complexity.OracleMachine

/-! Query counts are measured on the actual transition sequence, including
nonterminating or malformed-input prefixes. A decreasing finite potential gives
an upper bound without a syntactic count of query labels. -/
namespace Holant.Complexity.UniversalPairReduction.ThreeQuery

/-- The active command's query cost. Ordinary TM2 instructions cost zero queries. -/
def queryCost (m : OracleMachine) (c : m.Cfg) : ℕ :=
  match c.l with
  | none => 0
  | some l => match m.program l with
    | .ordinary _ => 0
    | .query _ => 1

/-- Number of actual oracle transitions in the first `n` steps from a configuration. -/
def queryCount (m : OracleMachine) (oracle : List Bool → List Bool) (c : m.Cfg) : ℕ → ℕ
  | 0 => 0
  | n+1 => match m.step oracle c with
    | none => 0
    | some d => queryCost m c + queryCount m oracle d n

/-- A per-transition potential proves a bound on every actual run prefix. -/
theorem queryCount_le_of_potential (m : OracleMachine) (oracle : List Bool → List Bool)
    (remaining : m.Cfg → ℕ)
    (hstep : ∀ c d, m.step oracle c = some d →
      queryCost m c + remaining d ≤ remaining c) (c : m.Cfg) (n : ℕ) :
    queryCount m oracle c n ≤ remaining c := by
  induction n generalizing c with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [queryCount]
    cases hs : m.step oracle c with
    | none => exact Nat.zero_le _
    | some d =>
      exact le_trans (Nat.add_le_add_left (ih d) _) (hstep c d hs)

/-- Uniform oracle-query bound, on arbitrary inputs, oracles and time prefixes. -/
def AtMostQueries (m : OracleMachine) (bound : ℕ) : Prop :=
  ∀ oracle input n, queryCount m oracle (m.init input) n ≤ bound

end Holant.Complexity.UniversalPairReduction.ThreeQuery
