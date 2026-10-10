import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem parse_edges (edges suffix : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 0) (Holant.Algebraic.frame edges++suffix) [] [] [] [] [])
      (ready m (.inr 2) suffix edges [] [] [] []) (2*(edges.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (edgesKey m) (temporaryKey m)
    (by simp [inputKey,edgesKey]) (by simp [inputKey,temporaryKey]) (by simp [edgesKey,temporaryKey])
    (TM2.step (program m)) (.inr 0) (.inr 1) (.inr 2) (.inr 47)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] [] []) edges suffix []
  simpa only [ready,config,tapes3,update_input,update_edges,update_temporary,List.append_nil] using h

theorem parse_target (edges target suffix : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 2) (Holant.Algebraic.frame target++suffix) edges [] [] [] [])
      (ready m (.inr 4) suffix edges target [] [] []) (2*(target.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (targetKey m) (temporaryKey m)
    (by simp [inputKey,targetKey]) (by simp [inputKey,temporaryKey]) (by simp [targetKey,temporaryKey])
    (TM2.step (program m)) (.inr 2) (.inr 3) (.inr 4) (.inr 47)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] edges [] [] [] [] [] [] []) target suffix []
  simpa only [ready,config,tapes3,update_input,update_target,update_temporary,List.append_nil] using h

theorem prepare (edges target rows : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 0) (Holant.Algebraic.frame edges++(Holant.Algebraic.frame target++rows)) [] [] [] [] [])
      (ready m (.inr 4) rows edges target [] [] []) (2*edges.length+2*target.length+4) := by
  have h := (parse_edges m edges (Holant.Algebraic.frame target++rows)).trans (parse_target m edges target rows)
  have ht : 2*edges.length+2*target.length+4=2*(target.length+1)+2*(edges.length+1) := by omega
  rw [ht]; exact h

theorem loop_marker (input edges target index rev output : List Bool) (bit : Bool) :
    TM2.step (program m) (ready m (.inr 4) (bit::input) edges target index rev output) =
      some (ready m (.inr (if bit then 5 else 30)) input edges target index rev output) := by
  cases bit <;>
    change some (cfg (.inr _ : Label m) m.initial (Function.update
      (tapes m (fun _ => []) (_::input) edges target index [] [] [] rev output) (inputKey m) input)) = _
  all_goals rw [update_input]; rfl

theorem parse_row (input edges target index rev output row : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 5) (Holant.Algebraic.frame row++input) edges target index rev output)
      (config m (.inr 7) (fun _ => []) input edges target index row [] [] rev output) (2*(row.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (rowKey m) (temporaryKey m)
    (by simp [inputKey,rowKey]) (by simp [inputKey,temporaryKey]) (by simp [rowKey,temporaryKey])
    (TM2.step (program m)) (.inr 5) (.inr 6) (.inr 7) (.inr 47)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] edges target index [] [] [] rev output) row input []
  simpa only [ready,config,tapes3,update_input,update_row,update_temporary,List.append_nil] using h
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
