import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem copy_edges (table cursor index edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 6) table cursor index edges output [])
      (config m (phase m 8) (wordTape m.input edges) table cursor index [] edges output [] []) (2*(edges.length+1)) := by
  have h := copy_exact_frame (edgesKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [edgesKey]) (by simp [edgesKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (phase m 6) (phase m 7) (phase m 8)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table cursor index [] [] output [] []) edges []
  simpa only [ready,config,tapes3,update_edges,update_source,update_temporary,
    NeighborCall.update_wordTape,NeighborCall.update_empty_source,NeighborCall.source_empty,List.append_nil] using h

theorem copy_index (source : m.K → List Bool) (table cursor index edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 8) source table cursor index [] edges output [] [])
      (config m (phase m 10) source table cursor index [] edges output index []) (2*(index.length+1)) := by
  have h := copy_exact_frame (indexKey m) (copyKey m) (temporaryKey m)
    (by simp [indexKey,copyKey]) (by simp [indexKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (phase m 8) (phase m 9) (phase m 10)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source table cursor [] [] edges output [] []) index []
  simpa only [config,tapes3,update_index,update_copy,update_temporary,List.append_nil] using h

theorem frame_index (table cursor index edges output suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 10) (wordTape m.input suffix) table cursor index [] edges output index [])
      (config m (phase m 13) (wordTape m.input (Holant.Algebraic.frame index++suffix)) table cursor index [] edges output [] [])
      (2*index.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey]) (by simp [copyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (phase m 10) (phase m 11) (phase m 12) (phase m 13)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table cursor index [] edges output [] []) index suffix
  simpa only [config,tapes3,update_copy,update_source,update_temporary,NeighborCall.update_wordTape] using h

theorem copy_table (source : m.K → List Bool) (table cursor index edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 13) source table cursor index [] edges output [] [])
      (config m (phase m 15) source table cursor index [] edges output table []) (2*(table.length+1)) := by
  have h := copy_exact_frame (tableKey m) (copyKey m) (temporaryKey m)
    (by simp [tableKey,copyKey]) (by simp [tableKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (phase m 13) (phase m 14) (phase m 15)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source [] cursor index [] edges output [] []) table []
  simpa only [config,tapes3,update_table,update_copy,update_temporary,List.append_nil] using h

theorem frame_table (table cursor index edges output suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 15) (wordTape m.input suffix) table cursor index [] edges output table [])
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame table++suffix)) table cursor index [] edges output [] [])
      (2*table.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey]) (by simp [copyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (phase m 15) (phase m 16) (phase m 17) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table cursor index [] edges output [] []) table suffix
  simpa only [config,tapes3,update_copy,update_source,update_temporary,NeighborCall.update_wordTape] using h

def queryWord (table index edges : List Bool) : List Bool :=
  Holant.Algebraic.frame table++(Holant.Algebraic.frame index++edges)

theorem prepare_query (table cursor index edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 6) table cursor index edges output [])
      (config m (.inl m.main) (wordTape m.input (queryWord table index edges)) table cursor index [] edges output [] [])
      (2*edges.length+4*index.length+4*table.length+12) := by
  have all := ((((copy_edges m table cursor index edges output).trans
    (copy_index m (wordTape m.input edges) table cursor index edges output)).trans
    (frame_index m table cursor index edges output edges)).trans
    (copy_table m (wordTape m.input (Holant.Algebraic.frame index++edges)) table cursor index edges output)).trans
    (frame_table m table cursor index edges output (Holant.Algebraic.frame index++edges))
  have ht : 2*edges.length+4*index.length+4*table.length+12 =
      (2*table.length+3)+(2*(table.length+1)+((2*index.length+3)+(2*(index.length+1)+2*(edges.length+1)))) := by omega
  rw [ht]
  exact all

theorem call_provider (table cursor index edges output result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (queryWord table index edges))) =
      some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inl m.main) (wordTape m.input (queryWord table index edges)) table cursor index [] edges output [] [])
      (config m (phase m 18) (wordTape m.output result) table cursor index [] edges output [] []) n := by
  let frame := extras table cursor index [] edges output [] []
  have run := Call.run (LeftMap.states m) Sum.inl (some (phase m 18)) m.program (program m)
    (fun _ => rfl) (initList m.computer (queryWord table index edges)) (haltList m.computer result) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (phase m 18))
      (initList m.computer (queryWord table index edges)) =
      config m (.inl m.main) (wordTape m.input (queryWord table index edges)) table cursor index [] edges output [] [] := by
    rw [Machine.init_eq]; rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (phase m 18))
      (haltList m.computer result) =
      config m (phase m 18) (wordTape m.output result) table cursor index [] edges output [] [] := by
    rw [Machine.halt_eq]; rfl
  rw [hi,ho] at run
  exact run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
