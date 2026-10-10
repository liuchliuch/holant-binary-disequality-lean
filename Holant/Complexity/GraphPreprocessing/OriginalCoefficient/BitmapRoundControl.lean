import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundQuery

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem loop_bit (table cursor index edges output : List Bool) (bit : Bool) :
    TM2.step (program m) (ready m (phase m 4) table (bit::cursor) (true::index) edges output []) =
      some (ready m (phase m (if bit then 5 else 6)) table cursor index edges output []) := by
  cases bit <;>
    change some (⟨some _,(none,m.initial),Function.update
      (Function.update (tapes m (fun _ => []) table (_::cursor) (true::index) [] edges output [] []) (indexKey m) index)
      (cursorKey m) cursor⟩ : (machine m).Config) = _
  all_goals simp only [update_index,update_cursor]; rfl

theorem true_round (table cursor index edges output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 4) table (true::cursor) (true::index) edges output [])
      (ready m (phase m 4) table cursor index edges (true::output) []) 2 := by
  have push : TM2.step (program m) (ready m (phase m 5) table cursor index edges output []) =
      some (ready m (phase m 4) table cursor index edges (true::output) []) := by
    change some (⟨some (phase m 4),(none,m.initial),Function.update
      (tapes m (fun _ => []) table cursor index [] edges output [] []) (outputKey m) (true::output)⟩ : (machine m).Config) = _
    rw [update_output]; rfl
  exact (runsExactly_one (loop_bit m table cursor index edges output true)).trans (runsExactly_one push)

theorem read_result (table cursor index edges output tail : List Bool) (bit : Bool) :
    TM2.step (program m)
      (config m (phase m 18) (wordTape m.output (bit::tail)) table cursor index [] edges output [] []) =
      some (config m (phase m 19) (wordTape m.output tail) table cursor index [] edges (bit::output) [] []) := by
  have hr : tapes m (wordTape m.output (bit::tail)) table cursor index [] edges output [] [] (.inl m.output) = bit::tail := by
    simp [tapes]
  have ho : tapes m (wordTape m.output tail) table cursor index [] edges output [] [] (outputKey m) = output := rfl
  simp [TM2.step,program,phase,outside,config,cfg,TM2.stepAux,hr,ho,update_source,NeighborCall.update_wordTape]

theorem drain_result (table cursor index edges output tail : List Bool) (bit : Bool) :
    RunsExactly (TM2.step (program m))
      (config m (phase m 18) (wordTape m.output (bit::tail)) table cursor index [] edges output [] [])
      (ready m (phase m 4) table cursor index edges (bit::output) []) (tail.length+2) := by
  have clear := clear_exact (TM2.step (program m)) (Sum.inl m.output : Stack m) (phase m 19) (phase m 4)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output tail) table cursor index [] edges (bit::output) [] [])
  rw [update_source,NeighborCall.update_wordTape,NeighborCall.source_empty] at clear
  have hk : tapes m (wordTape m.output tail) table cursor index [] edges (bit::output) [] [] (.inl m.output) = tail := by
    simp [tapes]
  rw [hk] at clear
  change RunsExactly (TM2.step (program m))
    (config m (phase m 19) (wordTape m.output tail) table cursor index [] edges (bit::output) [] [])
    (ready m (phase m 4) table cursor index edges (bit::output) []) (tail.length+1) at clear
  exact (runsExactly_one (read_result m table cursor index edges output tail bit)).trans clear

/-- A false old bit triggers one actual neighbor scan. Its option marker becomes
the new bit, and its remaining original-parent payload is physically erased. -/
theorem false_round (table cursor index edges output tail : List Bool) (bit : Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (queryWord table index edges))) =
      some (haltList m.computer (bit::tail))) :
    RunsExactly (TM2.step (program m))
      (ready m (phase m 4) table (false::cursor) (true::index) edges output [])
      (ready m (phase m 4) table cursor index edges (bit::output) [])
      (n+2*edges.length+4*index.length+4*table.length+tail.length+15) := by
  have all := (((runsExactly_one (loop_bit m table cursor index edges output false)).trans
    (prepare_query m table cursor index edges output)).trans
    (call_provider m table cursor index edges output (bit::tail) n h)).trans
    (drain_result m table cursor index edges output tail bit)
  have ht : n+2*edges.length+4*index.length+4*table.length+tail.length+15 =
      (tail.length+2)+(n+((2*edges.length+4*index.length+4*table.length+12)+1)) := by omega
  rw [ht]
  exact all

theorem loop_nil (table edges output : List Bool) :
    TM2.step (program m) (ready m (phase m 4) table [] [] edges output []) =
      some (ready m (phase m 25) table [] [] edges output []) := by
  change some (⟨some (phase m 25),(none,m.initial),Function.update
    (tapes m (fun _ => []) table [] [] [] edges output [] []) (indexKey m) []⟩ : (machine m).Config) = _
  rw [update_index]; rfl

theorem halt_step (output : List Bool) :
    TM2.step (program m) (ready m (phase m 28) [] [] [] [] output []) =
      some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have h := update_output m (fun _ => []) [] [] [] [] [] [] [] [] output
  rw [tapes_empty] at h
  change wordTape (outputKey m) output = _ at h
  change some (⟨none,(none,m.initial),tapes m (fun _ => []) [] [] [] [] [] output [] []⟩ : (machine m).Config) = _
  rw [← h]

theorem finish (table edges output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 4) table [] [] edges output [])
      (haltList (machine m).computer output) (table.length+edges.length+5) := by
  have a := clear_exact (TM2.step (program m)) (tableKey m) (phase m 25) (phase m 26)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) table [] [] [] edges output [] [])
  rw [update_table] at a
  have b := clear_exact (TM2.step (program m)) (edgesKey m) (phase m 26) (phase m 27)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) [] [] [] [] edges output [] [])
  rw [update_edges] at b
  have c := clear_exact (TM2.step (program m)) (cursorKey m) (phase m 27) (phase m 28)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) [] [] [] [] [] output [] [])
  rw [update_cursor] at c
  have all := ((((runsExactly_one (loop_nil m table edges output)).trans a).trans b).trans c).trans
    (runsExactly_one (halt_step m output))
  have ht : table.length+edges.length+5 = 1+(1+((edges.length+1)+((table.length+1)+1))) := by omega
  rw [ht]
  exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRound
