import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIteratePrepare

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines BitmapRound
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem loop_nil (table edges output : List Bool) :
    TM2.step (program m) (ready m (phase m 5) table [] [] edges output []) =
      some (ready m (phase m 18) table [] [] edges output []) := by
  change some (⟨some (phase m 18),(none,m.initial),Function.update
    (tapes m (fun _ => []) table [] [] [] edges output [] []) (indexKey m) []⟩ : (machine m).Config) = _
  rw [BitmapRound.update_index]; rfl

theorem halt_step (output : List Bool) :
    TM2.step (program m) (ready m (phase m 21) [] [] [] [] output []) =
      some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have h := BitmapRound.update_output m (fun _ => []) [] [] [] [] [] [] [] [] output
  rw [BitmapRound.tapes_empty] at h
  change wordTape (outputKey m) output = _ at h
  change some (⟨none,(none,m.initial),tapes m (fun _ => []) [] [] [] [] [] output [] []⟩ : (machine m).Config) = _
  rw [← h]

/-- The final bitmap is moved in order, after clearing the retained edge stream;
counter EOF, the empty-copy EOFs and the final halt are included. -/
theorem finish (table edges output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 5) table [] [] edges output [])
      (haltList (machine m).computer (table++output)) (edges.length+2*table.length+5) := by
  have clear := clear_exact (TM2.step (program m)) (edgesKey m) (phase m 18) (phase m 19)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) table [] [] [] edges output [] [])
  rw [BitmapRound.update_edges] at clear
  have move := transfer_exact_frame (tableKey m) (outputKey m) (temporaryKey m)
    (by simp [tableKey,outputKey,BitmapRound.tableKey,BitmapRound.outputKey])
    (by simp [tableKey,temporaryKey,BitmapRound.tableKey,BitmapRound.temporaryKey])
    (by simp [outputKey,temporaryKey,BitmapRound.outputKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 19) (phase m 20) (phase m 21)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] []) table output
  simp only [tapes3,BitmapRound.update_table,BitmapRound.update_output,BitmapRound.update_temporary] at move
  have all := (((runsExactly_one (loop_nil m table edges output)).trans clear).trans move).trans
    (runsExactly_one (halt_step m (table++output)))
  have ht : edges.length+2*table.length+5 = 1+(2*(table.length+1)+((edges.length+1)+1)) := by omega
  rw [ht]
  exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapIterate
