import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open BitmapRound
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem parse_table (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 0) [] [] [] [] [] (Holant.Algebraic.frame table++edges))
      (ready m (phase m 2) table [] [] [] [] edges) (2*(table.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (tableKey m) (temporaryKey m)
    (by simp [inputKey,tableKey,BitmapRound.inputKey,BitmapRound.tableKey]) (by simp [inputKey,temporaryKey,BitmapRound.inputKey,BitmapRound.temporaryKey]) (by simp [tableKey,temporaryKey,BitmapRound.tableKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 0) (phase m 1) (phase m 2) (phase m 31)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] []) table edges []
  simpa only [ready,config,tapes3,update_input,update_table,update_temporary,List.append_nil] using h

theorem retain_edges (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 2) table [] [] [] [] edges)
      (ready m (.inr (.inl 0)) table [] [] edges [] []) (2*(edges.length+1)) := by
  have h := transfer_exact_frame (inputKey m) (edgesKey m) (temporaryKey m)
    (by simp [inputKey,edgesKey,BitmapRound.inputKey,BitmapRound.edgesKey]) (by simp [inputKey,temporaryKey,BitmapRound.inputKey,BitmapRound.temporaryKey]) (by simp [edgesKey,temporaryKey,BitmapRound.edgesKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 2) (phase m 3) (.inr (.inl 0))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table [] [] [] [] [] [] []) edges []
  simpa only [ready,config,tapes3,update_input,update_edges,update_temporary,List.append_nil] using h

/-- The bitmap snapshot's real finite scan and restoration run inside the
controller, preserving the edge stream and output suffix; its halt is a return. -/
theorem snapshot_exact (table edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr (.inl 0)) table [] [] edges output [])
      (ready m (phase m 4) table table.reverse (List.replicate table.length true) edges output [])
      (2*table.length+3) := by
  let sourceLast : BitmapSnapshot.machine.Config :=
    ⟨none,(none,()),BitmapSnapshot.tapes table table.reverse (List.replicate table.length true) []⟩
  have a := BitmapSnapshot.exact_snapshot table [] []
  simp only [List.append_nil] at a
  have halt : TM2.step BitmapSnapshot.program
      (BitmapSnapshot.config 2 table table.reverse (List.replicate table.length true) []) = some sourceLast := rfl
  have source := a.trans (runsExactly_one halt)
  let frame := tapes m (fun _ => []) [] [] [] [] edges output [] []
  have run := Call.run_with_frame (snapshotLayout m (fun _ => [])) (snapshotLayout m frame) rfl
    (snapshotStates m) (fun l => .inr (.inl l)) (some (phase m 4)) BitmapSnapshot.program (program m)
    (fun _ => rfl) (BitmapSnapshot.config 0 table [] [] []) sourceLast _ source
  have hi : embedCfg (snapshotLayout m frame) (snapshotStates m) (fun l => .inr (.inl l)) (some (phase m 4))
      (BitmapSnapshot.config 0 table [] [] []) = ready m (.inr (.inl 0)) table [] [] edges output [] := by
    simp only [embedCfg,BitmapSnapshot.config,cfg,snapshotStates,Option.map_some,ready,config,frame,snapshot_lift]
    rfl
  have ho : embedCfg (snapshotLayout m frame) (snapshotStates m) (fun l => .inr (.inl l)) (some (phase m 4)) sourceLast =
      ready m (phase m 4) table table.reverse (List.replicate table.length true) edges output [] := by
    simp only [embedCfg,sourceLast,snapshotStates,Option.map_none,ready,config,cfg,frame,snapshot_lift]
    rfl
  rw [hi,ho] at run
  have ht : 2*table.length+3=1+2*(table.length+1) := by omega
  rw [ht]
  exact run

theorem prepare_snapshot (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 0) [] [] [] [] [] (Holant.Algebraic.frame table++edges))
      (ready m (phase m 4) table table.reverse (List.replicate table.length true) edges [] [])
      (4*table.length+2*edges.length+7) := by
  have all := ((parse_table m table edges).trans (retain_edges m table edges)).trans (snapshot_exact m table edges [])
  have ht : 4*table.length+2*edges.length+7 = (2*table.length+3)+(2*(edges.length+1)+2*(table.length+1)) := by omega
  rw [ht]
  exact all


theorem initial (input : List Bool) :
    initList (machine m).computer input = ready m (phase m 0) [] [] [] [] [] input := by
  rw [Machine.init_eq]
  have h := BitmapRound.update_input m (fun _ => []) [] [] [] [] [] [] [] [] input
  rw [BitmapRound.tapes_empty] at h
  change wordTape (inputKey m) input = _ at h
  unfold ready config cfg
  congr 1

theorem discard_cursor (table edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 4) table table.reverse (List.replicate table.length true) edges output [])
      (ready m (phase m 5) table [] (List.replicate table.length true) edges output []) (table.length+1) := by
  have h := clear_exact (TM2.step (program m)) (cursorKey m) (phase m 4) (phase m 5)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table table.reverse (List.replicate table.length true) [] edges output [] [])
  rw [BitmapRound.update_cursor] at h
  simpa [ready,config,tapes,extras,BitmapRound.cursorKey] using h

theorem prepare (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 0) [] [] [] [] [] (Holant.Algebraic.frame table++edges))
      (ready m (phase m 5) table [] (List.replicate table.length true) edges [] [])
      (5*table.length+2*edges.length+8) := by
  have h := (prepare_snapshot m table edges).trans (discard_cursor m table edges [])
  have ht : 5*table.length+2*edges.length+8 = (table.length+1)+(4*table.length+2*edges.length+7) := by omega
  rw [ht]
  exact h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
