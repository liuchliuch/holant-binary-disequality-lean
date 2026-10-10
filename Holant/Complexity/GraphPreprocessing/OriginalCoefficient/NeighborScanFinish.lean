import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanParse

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem halt_step (output : List Bool) :
    TM2.step (program m) (ready m (.inr 36) [] [] [] [] [] [] [] output) =
      some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have h := update_output m (fun _ => []) [] [] [] [] [] [] [] [] [] [] [] [] output
  rw [tapes_empty] at h
  change wordTape (outputKey m) output = _ at h
  change some (⟨none,(none,m.initial),tapes m (fun _ => []) [] [] [] [] [] [] [] [] [] [] [] output⟩ : (machine m).Config) = _
  rw [← h]

theorem cleanup (table target endpoint opposite input index output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 30) table target endpoint opposite input index [] output)
      (haltList (machine m).computer output)
      (input.length+table.length+target.length+endpoint.length+opposite.length+index.length+7) := by
  have a := clear_exact (TM2.step (program m)) (inputKey m) (.inr 30) (.inr 31)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target endpoint opposite [] [] [] input index [] [] output)
  rw [update_input] at a
  have b := clear_exact (TM2.step (program m)) (tableKey m) (.inr 31) (.inr 32)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target endpoint opposite [] [] [] [] index [] [] output)
  rw [update_table] at b
  have c := clear_exact (TM2.step (program m)) (targetKey m) (.inr 32) (.inr 33)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] target endpoint opposite [] [] [] [] index [] [] output)
  rw [update_target] at c
  have d := clear_exact (TM2.step (program m)) (endpointKey m) (.inr 33) (.inr 34)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] endpoint opposite [] [] [] [] index [] [] output)
  rw [update_endpoint] at d
  have e := clear_exact (TM2.step (program m)) (oppositeKey m) (.inr 34) (.inr 35)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] opposite [] [] [] [] index [] [] output)
  rw [update_opposite] at e
  have f := clear_exact (TM2.step (program m)) (indexKey m) (.inr 35) (.inr 36)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] [] index [] [] output)
  rw [update_index] at f
  have all := (((((a.trans b).trans c).trans d).trans e).trans f).trans (runsExactly_one (halt_step m output))
  have ht : input.length+table.length+target.length+endpoint.length+opposite.length+index.length+7 =
      1+((index.length+1)+((opposite.length+1)+((endpoint.length+1)+((target.length+1)+((table.length+1)+(input.length+1)))))) := by omega
  rw [ht]
  exact all

theorem no_neighbor (table target index output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 4) table target [] [] [] index [] output)
      (haltList (machine m).computer (false::output)) (table.length+target.length+index.length+9) := by
  have push : TM2.step (program m) (ready m (.inr 40) table target [] [] [] index [] output) =
      some (ready m (.inr 30) table target [] [] [] index [] (false::output)) := by
    change some (⟨some (.inr 30),(none,m.initial),Function.update
      (tapes m (fun _ => []) table target [] [] [] [] [] [] index [] [] output) (outputKey m) (false::output)⟩ : (machine m).Config) = _
    rw [update_output]; rfl
  have all := ((runsExactly_one (loop_nil m table target index output)).trans (runsExactly_one push)).trans
    (cleanup m table target [] [] [] index (false::output))
  have ht : table.length+target.length+index.length+9 =
      (([] : List Bool).length+table.length+target.length+([] : List Bool).length+([] : List Bool).length+index.length+7)+(1+1) := by simp
  rw [ht]
  exact all

def sideWord (side : Bool) : List Bool := if side then [true] else []

theorem emit_side (table target endpoint opposite input index output : List Bool) (side : Bool) :
    TM2.step (program m) (ready m (.inr 16) table target endpoint opposite input index (sideWord side) output) =
      some (ready m (.inr 17) table target endpoint opposite input index [] (side::output)) := by
  cases side <;>
    change some (⟨some (.inr 17),(none,m.initial),Function.update
      (Function.update (tapes m (fun _ => []) table target endpoint opposite [] [] [] input index [] _ output)
        (sideKey m) []) (outputKey m) (_::output)⟩ : (machine m).Config) = _
  all_goals rw [update_side,update_output]; rfl

theorem frame_index (table target endpoint opposite input index output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 17) table target endpoint opposite input index [] output)
      (ready m (.inr 20) table target endpoint opposite input [] [] (Holant.Algebraic.frame index++output)) (2*index.length+3) := by
  have h := FrameEmit.prepend_exact (indexKey m) (outputKey m) (temporaryKey m)
    (by simp [indexKey,outputKey]) (by simp [indexKey,temporaryKey]) (by simp [outputKey,temporaryKey])
    (TM2.step (program m)) (.inr 17) (.inr 18) (.inr 19) (.inr 20)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target endpoint opposite [] [] [] input [] [] [] []) index output
  simpa only [ready,config,tapes3,update_index,update_output,update_temporary] using h

theorem found (table target endpoint opposite input index output : List Bool) (side : Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 16) table target endpoint opposite input index (sideWord side) output)
      (haltList (machine m).computer (true::(Holant.Algebraic.frame index++side::output)))
      (2*index.length+input.length+table.length+target.length+endpoint.length+opposite.length+12) := by
  have push : TM2.step (program m)
      (ready m (.inr 20) table target endpoint opposite input [] [] (Holant.Algebraic.frame index++side::output)) =
      some (ready m (.inr 30) table target endpoint opposite input [] [] (true::(Holant.Algebraic.frame index++side::output))) := by
    change some (⟨some (.inr 30),(none,m.initial),Function.update
      (tapes m (fun _ => []) table target endpoint opposite [] [] [] input [] [] [] (Holant.Algebraic.frame index++side::output))
      (outputKey m) (true::(Holant.Algebraic.frame index++side::output))⟩ : (machine m).Config) = _
    rw [update_output]; rfl
  have all := (((runsExactly_one (emit_side m table target endpoint opposite input index output side)).trans
    (frame_index m table target endpoint opposite input index (side::output))).trans (runsExactly_one push)).trans
    (cleanup m table target endpoint opposite input [] (true::(Holant.Algebraic.frame index++side::output)))
  have ht : 2*index.length+input.length+table.length+target.length+endpoint.length+opposite.length+12 =
      (input.length+table.length+target.length+endpoint.length+opposite.length+([] : List Bool).length+7)+(1+((2*index.length+3)+1)) := by simp; omega
  rw [ht]
  exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
