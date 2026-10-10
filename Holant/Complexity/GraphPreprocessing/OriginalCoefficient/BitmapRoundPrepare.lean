import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem parse_table (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 0) [] [] [] [] [] (Holant.Algebraic.frame table++edges))
      (ready m (phase m 2) table [] [] [] [] edges) (2*(table.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (tableKey m) (temporaryKey m)
    (by simp [inputKey,tableKey]) (by simp [inputKey,temporaryKey]) (by simp [tableKey,temporaryKey])
    (TM2.step (program m)) (phase m 0) (phase m 1) (phase m 2) (phase m 31)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] []) table edges []
  simpa only [ready,config,tapes3,update_input,update_table,update_temporary,List.append_nil] using h

theorem retain_edges (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 2) table [] [] [] [] edges)
      (ready m (.inr (.inl 0)) table [] [] edges [] []) (2*(edges.length+1)) := by
  have h := transfer_exact_frame (inputKey m) (edgesKey m) (temporaryKey m)
    (by simp [inputKey,edgesKey]) (by simp [inputKey,temporaryKey]) (by simp [edgesKey,temporaryKey])
    (TM2.step (program m)) (phase m 2) (phase m 3) (.inr (.inl 0))
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table [] [] [] [] [] [] []) edges []
  simpa only [ready,config,tapes3,update_input,update_edges,update_temporary,List.append_nil] using h

theorem snapshot_lift (source : m.K → List Bool) (table cursor index scratch edges output copy input : List Bool) :
    (snapshotLayout m (tapes m source [] [] [] [] edges output copy input)).lift
      (BitmapSnapshot.tapes table cursor index scratch) = tapes m source table cursor index scratch edges output copy input := by
  funext k
  cases k with
  | inl k => rfl
  | inr k => fin_cases k <;> rfl

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

theorem prepare (table edges : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 0) [] [] [] [] [] (Holant.Algebraic.frame table++edges))
      (ready m (phase m 4) table table.reverse (List.replicate table.length true) edges [] [])
      (4*table.length+2*edges.length+7) := by
  have all := ((parse_table m table edges).trans (retain_edges m table edges)).trans (snapshot_exact m table edges [])
  have ht : 4*table.length+2*edges.length+7 = (2*table.length+3)+(2*(edges.length+1)+2*(table.length+1)) := by omega
  rw [ht]
  exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
