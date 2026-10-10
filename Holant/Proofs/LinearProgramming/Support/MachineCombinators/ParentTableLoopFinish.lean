import Holant.Proofs.LinearProgramming.Support.MachineCombinators.ParentTableLoopCalls

open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.ParentTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem clear_raw (raw output vertices : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 18) raw [] output vertices [])
      (cleanConfig m (.inr 22) [] [] output vertices []) (raw.length+1) := by
  have run := clear_exact (TM2.step (program m)) (rawKey m) (.inr 18) (.inr 22)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) raw [] output [] [] vertices [])
  rw [update_raw] at run
  exact run

theorem halt_step (output : List Bool) :
    TM2.step (program m) (cleanConfig m (.inr 22) [] [] output [] []) =
      some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have h := update_output m (fun _ => []) [] [] [] [] [] [] [] output
  rw [tapes_empty] at h
  change wordTape (outputKey m) output = _ at h
  change some (⟨none,(none,m.initial),tapes m (fun _ => []) [] [] output [] [] [] []⟩ :
    TM2.Cfg (fun _ : Stack m => Bool) (Label m) (Memory m)) = _
  rw [← h]

/-- The raw input is physically erased after the last indexed query. -/
theorem finish_exact (raw output : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 18) raw [] output [] [])
      (haltList (machine m).computer output) (raw.length+2) := by
  have all := (clear_raw m raw output []).trans (runsExactly_one (halt_step m output))
  have ht : raw.length+2=1+(raw.length+1) := by omega
  rw [ht]
  exact all

/-- Syntax-level failure uses a separate finite flag from every clean result. -/
theorem error_step (state : Memory m) (stack : Stack m → List Bool) :
    (machine m).computer.step (⟨some (.inr 23),state,stack⟩ : (machine m).Config) =
      some (⟨none,(some false,m.initial),stack⟩ : (machine m).Config) := rfl

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.ParentTableLoop
