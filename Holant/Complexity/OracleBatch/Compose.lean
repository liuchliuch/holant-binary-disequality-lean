import Holant.Complexity.OracleBatch.Execution

namespace Holant.Complexity.OracleBatch
open Turing Computability BinaryCompose Holant.Algebraic StackProtocol
variable (a b : BinaryCompose.Machine)

def overhead (oracle : List Bool → List Bool) (qs : List (List Bool)) (context : List Bool) : ℕ :=
  collectorCost oracle qs + 2 * ((word (qs.map oracle) context).length + 1)

/-- An actual preprocessor, a single fixed batch caller, and an actual
postprocessor form one clean finite-machine execution. -/
theorem run (oracle : List Bool → List Bool) (input : List Bool) (qs : List (List Bool))
    (context output : List Bool) (n m : ℕ)
    (ha : (fun p => p.bind a.computer.step)^[n] (some (initList a.computer input)) =
      some (haltList a.computer (word qs context)))
    (hb : (fun p => p.bind b.computer.step)^[m]
      (some (initList b.computer (word (qs.map oracle) context))) = some (haltList b.computer output)) :
    (fun p => p.bind ((machine a b).step oracle))^[m +
      (2 * ((word (qs.map oracle) context).length + 1) + (collectorCost oracle qs + n))]
      (some ((machine a b).init input)) = some ((machine a b).output output) := by
  have hfirst := OracleOneQuery.ordinary_run (M := machine a b)
    (leftLayout a b) (leftStates a b) (firstLabel a b) (some (admin a b 0))
    (fun _ => rfl) oracle _ _ n ha
  have hlast := OracleOneQuery.ordinary_run (M := machine a b)
    (rightLayout a b) (rightStates a b) (secondLabel a b) none
    (fun _ => rfl) oracle _ _ m hb
  change (fun p => p.bind ((machine a b).step oracle))^[n]
    (some (leftCfg a b _)) = some (leftCfg a b _) at hfirst
  change (fun p => p.bind ((machine a b).step oracle))^[m]
    (some (rightCfg a b _)) = some (rightCfg a b _) at hlast
  rw [left_init] at hfirst
  rw [right_halt] at hlast
  rw [Function.iterate_add_apply,Function.iterate_add_apply,Function.iterate_add_apply,
    hfirst,collector_run,transfer_run]
  exact hlast

def outputs (oracle : List Bool → List Bool) (input : List Bool) (qs : List (List Bool))
    (context output : List Bool) (n m : ℕ)
    (ha : TM2OutputsInTime a.computer input (some (word qs context)) n)
    (hb : TM2OutputsInTime b.computer (word (qs.map oracle) context) (some output) m) :
    (machine a b).OutputsInTime oracle input output (n + overhead oracle qs context + m) where
  steps := hb.steps + (2 * ((word (qs.map oracle) context).length + 1) +
    (collectorCost oracle qs + ha.steps))
  evals_in_steps := run a b oracle input qs context output ha.steps hb.steps
    ha.evals_in_steps hb.evals_in_steps
  steps_le_m := by have := ha.steps_le_m; have := hb.steps_le_m; simp only [overhead]; omega

/-- Length accounting includes every list marker, including empty answers. -/
theorem loopCost_le (oracle : List Bool → List Bool) (qs : List (List Bool)) :
    loopCost oracle qs ≤ 4 * (listWord qs).length + (listWord (qs.map oracle)).length := by
  induction qs with
  | nil => simp [loopCost,listWord,entries]
  | cons q qs ih =>
    simp only [loopCost,List.map_cons,listWord_cons,List.length_cons,List.length_append,frame_length]
    omega

theorem overhead_le (oracle : List Bool → List Bool) (qs : List (List Bool)) (context : List Bool) :
    overhead oracle qs context ≤ 16 * ((word qs context).length + (word (qs.map oracle) context).length + 1) := by
  have h := loopCost_le oracle qs
  simp only [overhead,collectorCost,word,List.length_append,frame_length]
  omega

/-- This bound counts elementary instructions in every actual ordinary command.
The fixed factor depends only on the finite caller and its two finite programs. -/
theorem primitive_command_bound (label : (machine a b).Λ)
    (stmt : TM2.Stmt (fun _ : (machine a b).K => Bool) (machine a b).Λ (machine a b).σ)
    (h : (machine a b).program label = .ordinary stmt)
    (state : (machine a b).σ) (ts : (machine a b).K → List Bool) :
    (TM2Cost.primitiveRun stmt state ts).1 ≤ (machine a b).primitiveBudget :=
  OracleMachine.ordinary_cost_le _ label stmt h state ts

end Holant.Complexity.OracleBatch
