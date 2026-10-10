import Holant.Complexity.OracleMachine

/-! # Input/output/control entry choices do not change oracle transition semantics -/

namespace Holant.Complexity.OracleMachine

abbrev withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ) : OracleMachine :=
  { m with inputStack := input, outputStack := output, main := main }

/-- Entry/output metadata changes initialization and observation, not the program. -/
theorem step_withEntry (m : OracleMachine) (input output : m.K) (main : m.Λ)
    (oracle : List Bool → List Bool) :
    (m.withEntry input output main).step oracle = m.step oracle := by
  funext c
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    cases hc : m.program label <;> simp [step, withEntry, hc]

end Holant.Complexity.OracleMachine
