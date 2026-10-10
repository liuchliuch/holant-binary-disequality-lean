import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchCall

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines BitmapRound
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem loop_cons (table index edges depth : List Bool) :
    TM2.step (program m) (ready m (phase m 5) table [] (true::index) edges depth []) =
      some (ready m (phase m 6) table [] index edges (true::depth) []) := by
  change some (⟨some (phase m 6),(none,m.initial),Function.update (Function.update
    (tapes m (fun _ => []) table [] (true::index) [] edges depth [] []) (indexKey m) index)
      (outputKey m) (true::depth)⟩ : (machine m).Config) = _
  rw [BitmapRound.update_index,BitmapRound.update_output]; rfl

theorem parse_result (table index edges depth next parent : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 13) (wordTape m.output (Holant.Algebraic.frame next++parent)) table [] index [] edges depth [] [])
      (config m (phase m 15) (wordTape m.output parent) table next index [] edges depth [] []) (2*(next.length+1)) := by
  have h := Frame.extract_exact (Sum.inl m.output : Stack m) (cursorKey m) (temporaryKey m)
    (by simp [cursorKey,BitmapRound.cursorKey]) (by simp [temporaryKey,BitmapRound.temporaryKey])
    (by simp [cursorKey,temporaryKey,BitmapRound.cursorKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 13) (phase m 14) (phase m 15) (phase m 31)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output []) table [] index [] edges depth [] []) next parent []
  simpa only [config,tapes3,update_source,update_cursor,update_temporary,
    NeighborCall.update_wordTape,List.append_nil] using h

theorem marker_false (table next index edges depth : List Bool) :
    TM2.step (program m)
      (config m (phase m 15) (wordTape m.output [false]) table next index [] edges depth [] []) =
        some (ready m (phase m 16) table next index edges depth []) := by
  have hr : tapes m (wordTape m.output [false]) table next index [] edges depth [] [] (.inl m.output) = [false] := by simp [tapes]
  simp [TM2.step,program,phase,outside,config,ready,cfg,TM2.stepAux,hr,update_source,
    NeighborCall.update_wordTape,NeighborCall.source_empty]

theorem marker_true (table next index edges depth parent : List Bool) :
    TM2.step (program m)
      (config m (phase m 15) (wordTape m.output (true::parent)) table next index [] edges depth [] []) =
        some (config m (phase m 22) (wordTape m.output parent) table next index [] edges depth [] []) := by
  have hr : tapes m (wordTape m.output (true::parent)) table next index [] edges depth [] [] (.inl m.output) = true::parent := by simp [tapes]
  simp [TM2.step,program,phase,outside,config,cfg,TM2.stepAux,hr,update_source,NeighborCall.update_wordTape]

theorem restore_marker (table next index edges depth parent : List Bool) :
    TM2.step (program m)
      (config m (phase m 22) (wordTape m.output parent) table next index [] edges depth [] []) =
        some (config m (phase m 23) (wordTape m.output (true::parent)) table next index [] edges depth [] []) := by
  have hr : tapes m (wordTape m.output parent) table next index [] edges depth [] [] (.inl m.output) = parent := by simp [tapes]
  simp [TM2.step,program,phase,outside,config,cfg,TM2.stepAux,hr,update_source,NeighborCall.update_wordTape]

theorem replace_table (table next index edges depth : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 16) table next index edges depth [])
      (ready m (phase m 5) next [] index edges depth []) (table.length+2*next.length+3) := by
  have clear := clear_exact (TM2.step (program m)) (tableKey m) (phase m 16) (phase m 17)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) table next index [] edges depth [] [])
  rw [BitmapRound.update_table] at clear
  have move := transfer_exact_frame (cursorKey m) (tableKey m) (temporaryKey m)
    (by simp [cursorKey,tableKey,BitmapRound.cursorKey,BitmapRound.tableKey])
    (by simp [cursorKey,temporaryKey,BitmapRound.cursorKey,BitmapRound.temporaryKey])
    (by simp [tableKey,temporaryKey,BitmapRound.tableKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 17) (phase m 18) (phase m 5)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] index [] edges depth [] []) next []
  simp only [tapes3,update_cursor,update_table,update_temporary,List.append_nil] at move
  have ht : table.length+2*next.length+3 = 2*(next.length+1)+(table.length+1) := by omega
  rw [ht]
  exact clear.trans move

theorem miss_exact (table next index edges depth : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (Holant.Algebraic.frame table++edges))) =
      some (haltList m.computer (Holant.Algebraic.frame next++[false]))) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 5) table [] (true::index) edges depth [])
      (ready m (phase m 5) next [] index edges (true::depth) [])
      (n+2*edges.length+5*table.length+4*next.length+14) := by
  have all := (((((runsExactly_one (loop_cons m table index edges depth)).trans
    (prepare_query m table index edges (true::depth))).trans
    (call_provider m table index edges (true::depth) (Holant.Algebraic.frame next++[false]) n h)).trans
    (parse_result m table index edges (true::depth) next [false])).trans
    (runsExactly_one (marker_false m table next index edges (true::depth)))).trans
    (replace_table m table next index edges (true::depth))
  convert all using 1 <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
