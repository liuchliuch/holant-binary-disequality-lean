import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearchPrepare

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines BitmapRound
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem copy_edges (table index edges output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 6) table [] index edges output [])
      (config m (phase m 8) (wordTape m.input edges) table [] index [] edges output [] []) (2*(edges.length+1)) := by
  have h := copy_exact_frame (edgesKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [edgesKey,BitmapRound.edgesKey])
    (by simp [edgesKey,temporaryKey,BitmapRound.edgesKey,BitmapRound.temporaryKey])
    (by simp [temporaryKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 6) (phase m 7) (phase m 8)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table [] index [] [] output [] []) edges []
  simpa only [ready,config,tapes3,update_edges,update_source,update_temporary,
    NeighborCall.update_wordTape,NeighborCall.update_empty_source,NeighborCall.source_empty,List.append_nil] using h

theorem copy_table (source : m.K → List Bool) (table index edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 8) source table [] index [] edges output [] [])
      (config m (phase m 10) source table [] index [] edges output table []) (2*(table.length+1)) := by
  have h := copy_exact_frame (tableKey m) (copyKey m) (temporaryKey m)
    (by simp [tableKey,copyKey,BitmapRound.tableKey,BitmapRound.copyKey])
    (by simp [tableKey,temporaryKey,BitmapRound.tableKey,BitmapRound.temporaryKey])
    (by simp [copyKey,temporaryKey,BitmapRound.copyKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 8) (phase m 9) (phase m 10)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source [] [] index [] edges output [] []) table []
  simpa only [config,tapes3,update_table,update_copy,update_temporary,List.append_nil] using h

theorem frame_table (table index edges output suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 10) (wordTape m.input suffix) table [] index [] edges output table [])
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame table++suffix)) table [] index [] edges output [] [])
      (2*table.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey,BitmapRound.copyKey])
    (by simp [copyKey,temporaryKey,BitmapRound.copyKey,BitmapRound.temporaryKey])
    (by simp [temporaryKey,BitmapRound.temporaryKey])
    (TM2.step (program m)) (phase m 10) (phase m 11) (phase m 12) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table [] index [] edges output [] []) table suffix
  simpa only [config,tapes3,update_copy,update_source,update_temporary,NeighborCall.update_wordTape] using h

theorem prepare_query (table index edges output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 6) table [] index edges output [])
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame table++edges)) table [] index [] edges output [] [])
      (2*edges.length+4*table.length+7) := by
  have h := ((copy_edges m table index edges output).trans
    (copy_table m (wordTape m.input edges) table index edges output)).trans (frame_table m table index edges output edges)
  have ht : 2*edges.length+4*table.length+7 = (2*table.length+3)+(2*(table.length+1)+2*(edges.length+1)) := by omega
  rw [ht]; exact h

theorem call_provider (table index edges output result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (Holant.Algebraic.frame table++edges))) =
      some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame table++edges)) table [] index [] edges output [] [])
      (config m (phase m 13) (wordTape m.output result) table [] index [] edges output [] []) n := by
  let frame := extras table [] index [] edges output [] []
  have run := Call.run (LeftMap.states m) Sum.inl (some (phase m 13)) m.program (program m)
    (fun _ => rfl) (initList m.computer (Holant.Algebraic.frame table++edges)) (haltList m.computer result) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (phase m 13))
      (initList m.computer (Holant.Algebraic.frame table++edges)) =
      config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame table++edges)) table [] index [] edges output [] [] := by
    rw [Machine.init_eq]; rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (phase m 13))
      (haltList m.computer result) =
      config m (phase m 13) (wordTape m.output result) table [] index [] edges output [] [] := by
    rw [Machine.halt_eq]; rfl
  rw [hi,ho] at run
  exact run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentSearch
