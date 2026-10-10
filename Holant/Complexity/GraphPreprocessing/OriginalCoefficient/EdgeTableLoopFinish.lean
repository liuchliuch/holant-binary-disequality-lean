import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoopCalls

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem clear_raw (raw output vertices : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 18) raw [] output vertices [])
      (cleanConfig m (.inr 19) [] [] output vertices []) (raw.length+1) := by
  have run := clear_exact (TM2.step (program m)) (rawKey m) (.inr 18) (.inr 19)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) raw [] output [] [] vertices [])
  rw [update_raw] at run
  exact run

theorem frame_vertices (output vertices : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 19) [] [] output vertices [])
      (cleanConfig m (.inr 22) [] [] (Holant.Algebraic.frame vertices ++ output) [] []) (2*vertices.length+3) := by
  have run := FrameEmit.prepend_exact (verticesKey m) (outputKey m) (temporaryKey m)
    (by simp [verticesKey,outputKey]) (by simp [verticesKey,temporaryKey]) (by simp [outputKey,temporaryKey])
    (TM2.step (program m)) (.inr 19) (.inr 20) (.inr 21) (.inr 22)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] []) vertices output
  simpa only [cleanConfig,config,tapes3,update_vertices,update_output,update_temporary] using run

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

/-- Original raw data is erased and the original vertex count is retained in
its exact frame, so isolated/nullary vertices are not lost. -/
theorem finish_exact (raw output vertices : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 18) raw [] output vertices [])
      (haltList (machine m).computer (Holant.Algebraic.frame vertices ++ output))
      (raw.length+2*vertices.length+5) := by
  have all := ((clear_raw m raw output vertices).trans (frame_vertices m output vertices)).trans
    (runsExactly_one (halt_step m (Holant.Algebraic.frame vertices ++ output)))
  have ht : raw.length+2*vertices.length+5 = 1+(2*vertices.length+3+(raw.length+1)) := by omega
  rw [ht]
  exact all

/-- Syntax-level failure uses a separate finite flag from every clean result. -/
theorem error_step (state : Memory m) (stack : Stack m → List Bool) :
    (machine m).computer.step (⟨some (.inr 23),state,stack⟩ : (machine m).Config) =
      some (⟨none,(some false,m.initial),stack⟩ : (machine m).Config) := rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
