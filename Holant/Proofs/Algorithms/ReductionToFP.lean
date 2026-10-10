import Holant.Proofs.Algorithms.OrdinaryOracle


namespace Holant.LocalDrafts.MainChain.ReductionToFP
open Computability Holant.Complexity Holant.Complexity.BinaryCompose
open OrdinaryOracle

/-- Every external query of the inliner would have to come from its callee.
The protocol and compiled caller commands are explicitly ordinary statements. -/
theorem composed_ordinary (callee caller : OracleMachine) (hc : AllOrdinary callee) :
    AllOrdinary (OracleCompose.machine callee caller) := by
  intro l
  rcases l with l | (phase | label)
  · obtain ⟨q,hq⟩ := hc l
    simp [OracleCompose.machine, OracleCompose.base, OracleMachine.withEntry,
      OracleInline.machine, OracleInline.rawMachine, OracleStateRename.machine,
      OracleStateRename.command, OracleSubroutine.machine, hq]
  · simp [OracleCompose.machine, OracleCompose.base, OracleMachine.withEntry,
      OracleInline.machine, OracleInline.rawMachine, OracleStateRename.machine,
      OracleStateRename.command, OracleSubroutine.machine]
  · change ∃ q, (OracleCompose.base callee caller).program (.inr (.inr label)) = .ordinary q
    rw [OracleInline.program_outside]
    unfold OracleCompose.outside
    cases caller.program label <;> exact ⟨_,rfl⟩

variable {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}

/-- The time includes copying queries, running the actual evaluator, clearing
stale answers and returning encoded results. Erasure changes no transitions. -/
noncomputable def computes (r : LengthControlledOracleReduction ea eb ec ed f g)
    (a : Computes ec ed g) : Computes ea eb f :=
  eraseReduction (r.compose (liftReduction a))
    (composed_ordinary (lift a.machine) r.reduction.machine (lift_ordinary a.machine))

theorem inFP (r : LengthControlledOracleReduction ea eb ec ed f g)
    (a : Computes ec ed g) : InFP ea eb f := (computes r a).inFP

end Holant.LocalDrafts.MainChain.ReductionToFP
