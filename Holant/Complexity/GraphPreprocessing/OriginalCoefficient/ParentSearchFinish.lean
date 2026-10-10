import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchControl

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines BitmapRound
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem clear_success (table next index edges depth parent : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 23) (wordTape m.output parent) table next index [] edges depth [] [])
      (config m (phase m 27) (wordTape m.output parent) [] [] [] [] [] depth [] [])
      (table.length+next.length+index.length+edges.length+4) := by
  have a := clear_exact (TM2.step (program m)) (tableKey m) (phase m 23) (phase m 24)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (wordTape m.output parent) table next index [] edges depth [] [])
  rw [BitmapRound.update_table] at a
  change RunsExactly (TM2.step (program m)) _ _ (table.length+1) at a
  have b := clear_exact (TM2.step (program m)) (cursorKey m) (phase m 24) (phase m 25)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (wordTape m.output parent) [] next index [] edges depth [] [])
  rw [BitmapRound.update_cursor] at b
  change RunsExactly (TM2.step (program m)) _ _ (next.length+1) at b
  have c := clear_exact (TM2.step (program m)) (indexKey m) (phase m 25) (phase m 26)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (wordTape m.output parent) [] [] index [] edges depth [] [])
  rw [BitmapRound.update_index] at c
  change RunsExactly (TM2.step (program m)) _ _ (index.length+1) at c
  have d := clear_exact (TM2.step (program m)) (edgesKey m) (phase m 26) (phase m 27)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (wordTape m.output parent) [] [] [] [] edges depth [] [])
  rw [BitmapRound.update_edges] at d
  change RunsExactly (TM2.step (program m)) _ _ (edges.length+1) at d
  have ht : table.length+next.length+index.length+edges.length+4 =
      (edges.length+1)+((index.length+1)+((next.length+1)+(table.length+1))) := by omega
  rw [ht]
  exact ((a.trans b).trans c).trans d

theorem frame_depth (depth parent : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 27) (wordTape m.output parent) [] [] [] [] [] depth [] [])
      (config m (phase m 30) (wordTape m.output (Holant.Algebraic.frame depth++parent)) [] [] [] [] [] [] [] [])
      (2*depth.length+3) := by
  have h := FrameEmit.prepend_exact (outputKey m) (Sum.inl m.output : Stack m) (temporaryKey m)
    (by simp [outputKey,BitmapRound.outputKey])
    (by simp [outputKey,temporaryKey,BitmapRound.outputKey,BitmapRound.temporaryKey])
    (by simp [temporaryKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 27) (phase m 28) (phase m 29) (phase m 30)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output []) [] [] [] [] [] [] [] []) depth parent
  simpa only [config,tapes3,update_output,update_source,update_temporary,NeighborCall.update_wordTape] using h

theorem halt_step (output : List Bool) :
    TM2.step (program m)
      (config m (phase m 30) (wordTape m.output output) [] [] [] [] [] [] [] []) =
        some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have h := BitmapRound.update_source m (fun _ => []) [] [] [] [] [] [] [] [] m.output output
  rw [BitmapRound.tapes_empty,NeighborCall.update_empty_source] at h
  change wordTape (Sum.inl m.output : Stack m) output = _ at h
  change some (⟨none,(none,m.initial),tapes m (wordTape m.output output) [] [] [] [] [] [] [] []⟩ : (machine m).Config) = _
  rw [←h]

theorem finish_success (table next index edges depth parent : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 23) (wordTape m.output parent) table next index [] edges depth [] [])
      (haltList (machine m).computer (Holant.Algebraic.frame depth++parent))
      (table.length+next.length+index.length+edges.length+2*depth.length+8) := by
  have all := ((clear_success m table next index edges depth parent).trans
    (frame_depth m depth parent)).trans (runsExactly_one (halt_step m (Holant.Algebraic.frame depth++parent)))
  convert all using 1 <;> omega

theorem found_exact (table next index edges depth parent : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (Holant.Algebraic.frame table++edges))) =
      some (haltList m.computer (Holant.Algebraic.frame next++true::parent))) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 5) table [] (true::index) edges depth [])
      (haltList (machine m).computer (Holant.Algebraic.frame (true::depth)++true::parent))
      (n+3*edges.length+5*table.length+3*next.length+index.length+2*depth.length+22) := by
  have all := ((((((runsExactly_one (loop_cons m table index edges depth)).trans
    (prepare_query m table index edges (true::depth))).trans
    (call_provider m table index edges (true::depth) (Holant.Algebraic.frame next++true::parent) n h)).trans
    (parse_result m table index edges (true::depth) next (true::parent))).trans
    (runsExactly_one (marker_true m table next index edges (true::depth) parent))).trans
    (runsExactly_one (restore_marker m table next index edges (true::depth) parent))).trans
    (finish_success m table next index edges (true::depth) (true::parent))
  convert all using 1 <;> simp only [List.length_cons] <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
