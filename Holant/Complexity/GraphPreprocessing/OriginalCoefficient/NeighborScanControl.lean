import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanParse
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanCall

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem result_step (table target endpoint opposite input index side output : List Bool) (bit : Bool) :
    TM2.step (program m)
      (config m (.inr 7) (wordTape m.output [bit]) table target endpoint opposite [] [] [] input index [] side output) =
      some (ready m (.inr (if bit then 16 else 8)) table target endpoint opposite input index side output) := by
  have hr : tapes m (wordTape m.output [bit]) table target endpoint opposite [] [] [] input index [] side output (resultKey m) = [bit] := by
    simp [tapes,NeighborCall.tapes,resultKey]
  change tapes m (wordTape m.output [bit]) table target endpoint opposite [] [] [] input index [] side output
    (.inl (.inl m.output)) = [bit] at hr
  cases bit <;>
    simp [TM2.step,program,Returning.program,outside,config,cfg,TM2.stepAux,hr,
      ready,resultKey,update_source,NeighborCall.update_wordTape,NeighborCall.source_empty]

theorem first_failed (table target endpoint opposite input index output : List Bool) :
    TM2.step (program m) (ready m (.inr 8) table target endpoint opposite input index [] output) =
      some (ready m (.inr 9) table target endpoint opposite input index [] output) := by
  change some (⟨some (.inr 9),(none,m.initial),Function.update
    (tapes m (fun _ => []) table target endpoint opposite [] [] [] input index [] [] output) (sideKey m) []⟩ : (machine m).Config) = _
  rw [update_side]
  rfl

theorem second_failed (table target endpoint opposite input index output : List Bool) :
    TM2.step (program m) (ready m (.inr 8) table target endpoint opposite input index [true] output) =
      some (ready m (.inr 22) table target endpoint opposite input index [] output) := by
  change some (⟨some (.inr 22),(none,m.initial),Function.update
    (tapes m (fun _ => []) table target endpoint opposite [] [] [] input index [] [true] output) (sideKey m) []⟩ : (machine m).Config) = _
  rw [update_side]
  rfl

theorem swap_ends (table target endpoint opposite input index output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 9) table target endpoint opposite input index [] output)
      (ready m (.inl (.inr 0)) table target opposite endpoint input index [true] output)
      (4*endpoint.length+2*opposite.length+7) := by
  have a := transfer_exact_frame (endpointKey m) (holdKey m) (temporaryKey m)
    (by simp [endpointKey,holdKey]) (by simp [endpointKey,temporaryKey,NeighborCall.endpointKey,NeighborCall.temporaryKey])
    (by simp [holdKey,temporaryKey]) (TM2.step (program m)) (.inr 9) (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target [] opposite [] [] [] input index [] [] output) endpoint []
  simp only [tapes3,update_endpoint,update_hold,update_temporary,List.append_nil] at a
  have b := transfer_exact_frame (oppositeKey m) (endpointKey m) (temporaryKey m)
    (by simp [oppositeKey,endpointKey,NeighborCall.oppositeKey,NeighborCall.endpointKey])
    (by simp [oppositeKey,temporaryKey,NeighborCall.oppositeKey,NeighborCall.temporaryKey])
    (by simp [endpointKey,temporaryKey,NeighborCall.endpointKey,NeighborCall.temporaryKey])
    (TM2.step (program m)) (.inr 11) (.inr 12) (.inr 13)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target [] [] [] [] [] input index endpoint [] output) opposite []
  simp only [tapes3,update_opposite,update_endpoint,update_temporary,List.append_nil] at b
  have c := transfer_exact_frame (holdKey m) (oppositeKey m) (temporaryKey m)
    (by simp [holdKey,oppositeKey]) (by simp [holdKey,temporaryKey])
    (by simp [oppositeKey,temporaryKey,NeighborCall.oppositeKey,NeighborCall.temporaryKey])
    (TM2.step (program m)) (.inr 13) (.inr 14) (.inr 15)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target opposite [] [] [] [] input index [] [] output) endpoint []
  simp only [tapes3,update_hold,update_opposite,update_temporary,List.append_nil] at c
  have d : TM2.step (program m) (ready m (.inr 15) table target opposite endpoint input index [] output) =
      some (ready m (.inl (.inr 0)) table target opposite endpoint input index [true] output) := by
    change some (⟨some (.inl (.inr 0)),(none,m.initial),Function.update
      (tapes m (fun _ => []) table target opposite endpoint [] [] [] input index [] [] output) (sideKey m) [true]⟩ : (machine m).Config) = _
    rw [update_side]; rfl
  have all := ((a.trans b).trans c).trans (runsExactly_one d)
  have ht : 4*endpoint.length+2*opposite.length+7 =
      1+(2*(endpoint.length+1)+(2*(opposite.length+1)+2*(endpoint.length+1))) := by omega
  rw [ht]
  exact all

theorem advance_edge (table target endpoint opposite input index output : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 22) table target endpoint opposite input index [] output)
      (ready m (.inr 4) table target [] [] input (true::index) [] output)
      (endpoint.length+opposite.length+3) := by
  have a := clear_exact (TM2.step (program m)) (endpointKey m) (.inr 22) (.inr 23)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target endpoint opposite [] [] [] input index [] [] output)
  rw [update_endpoint] at a
  have b := clear_exact (TM2.step (program m)) (oppositeKey m) (.inr 23) (.inr 24)
    (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table target [] opposite [] [] [] input index [] [] output)
  rw [update_opposite] at b
  have c : TM2.step (program m) (ready m (.inr 24) table target [] [] input index [] output) =
      some (ready m (.inr 4) table target [] [] input (true::index) [] output) := by
    change some (⟨some (.inr 4),(none,m.initial),Function.update
      (tapes m (fun _ => []) table target [] [] [] [] [] input index [] [] output) (indexKey m) (true::index)⟩ : (machine m).Config) = _
    rw [update_index]; rfl
  have ht : endpoint.length+opposite.length+3 = 1+((opposite.length+1)+(endpoint.length+1)) := by omega
  rw [ht]
  exact (a.trans b).trans (runsExactly_one c)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
