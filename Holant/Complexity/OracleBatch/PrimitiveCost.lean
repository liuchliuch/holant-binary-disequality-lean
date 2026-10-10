import Holant.Complexity.OracleBatch.Program

namespace Holant.Complexity.OracleBatch
open Turing BinaryCompose

/-- Count the actual branch's elementary stack operations, charging one for an
oracle invocation. Oracle answer bit handling remains in ordinary instructions. -/
def primitiveStepCost (m : OracleMachine) (c : m.Cfg) : ℕ :=
  match c.l with
  | none => 0
  | some l => match m.program l with
    | .ordinary stmt => (TM2Cost.primitiveRun stmt c.var c.stk).1
    | .query _ => 1

def primitiveCount (m : OracleMachine) (oracle : List Bool → List Bool) (c : m.Cfg) : ℕ → ℕ
  | 0 => 0
  | n+1 => match m.step oracle c with
    | none => 0
    | some d => primitiveStepCost m c + primitiveCount m oracle d n

theorem primitiveStepCost_le (m : OracleMachine) (c : m.Cfg) :
    primitiveStepCost m c ≤ m.primitiveBudget := by
  rcases c with ⟨l,v,s⟩
  cases l with
  | none => exact Nat.zero_le _
  | some l =>
    cases h : m.program l with
    | ordinary stmt =>
      simpa [primitiveStepCost,h] using m.ordinary_cost_le l stmt h v s
    | query next =>
      simpa [primitiveStepCost,OracleMachine.commandBudget,h] using m.commandBudget_le l

theorem primitiveCount_le (m : OracleMachine) (oracle : List Bool → List Bool)
    (c : m.Cfg) (n : ℕ) : primitiveCount m oracle c n ≤ m.primitiveBudget * n := by
  induction n generalizing c with
  | zero => simp [primitiveCount]
  | succ n ih =>
    cases h : m.step oracle c with
    | none => simp [primitiveCount,h]
    | some d =>
      have hs := primitiveStepCost_le m c
      have hn := ih d
      simp only [primitiveCount,h,Nat.mul_succ]
      omega

/-- Every administrative transition uses at most eight elementary instructions,
independently of query count and all query, answer and context lengths. -/
theorem protocol_budget_le (a b : BinaryCompose.Machine) (i : Fin 17) :
    (machine a b).commandBudget (admin a b i) ≤ 8 := by
  fin_cases i <;> simp [OracleMachine.commandBudget,machine,program,admin,protocol,
    dispatchStmt,reverseEmitStmt,GraphPreprocessing.Frame.scanStmt,
    StackProtocol.copyMoveStmt,FixedFieldMachines.FrameEmit.delimiterStmt,
    FixedFieldMachines.FrameEmit.emitStmt,TM2Cost.budget]

end Holant.Complexity.OracleBatch
