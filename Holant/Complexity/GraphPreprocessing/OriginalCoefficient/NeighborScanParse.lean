import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def ready (label : Label m) (table target endpoint opposite input index side output : List Bool) :=
  config m label (fun _ => []) table target endpoint opposite [] [] [] input index [] side output

theorem tapes_empty : tapes m (fun _ => []) [] [] [] [] [] [] [] [] [] [] [] [] = fun _ => [] := by
  funext k
  rcases k with (k|k)|k
  · rfl
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl

theorem initial (input : List Bool) :
    initList (machine m).computer input = ready m (.inr 0) [] [] [] [] input [] [] [] := by
  rw [Machine.init_eq]
  have h := update_input m (fun _ => []) [] [] [] [] [] [] [] [] [] [] [] [] input
  rw [tapes_empty] at h
  change wordTape (inputKey m) input = _ at h
  unfold ready config cfg
  congr 1

theorem parse_table (table suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 0) [] [] [] [] (Holant.Algebraic.frame table++suffix) [] [] [])
      (ready m (.inr 2) table [] [] [] suffix [] [] []) (2*(table.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (tableKey m) (temporaryKey m)
    (by simp [inputKey,tableKey]) (by simp [inputKey,temporaryKey]) (by simp [tableKey,temporaryKey,NeighborCall.tableKey,NeighborCall.temporaryKey])
    (TM2.step (program m)) (.inr 0) (.inr 1) (.inr 2) (.inr 47)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] [] [] [] [] []) table suffix []
  simpa only [ready,config,tapes3,update_input,update_table,update_temporary,List.append_nil] using h

theorem parse_target (table target suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 2) table [] [] [] (Holant.Algebraic.frame target++suffix) [] [] [])
      (ready m (.inr 4) table target [] [] suffix [] [] []) (2*(target.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (targetKey m) (temporaryKey m)
    (by simp [inputKey,targetKey]) (by simp [inputKey,temporaryKey]) (by simp [targetKey,temporaryKey,NeighborCall.targetKey,NeighborCall.temporaryKey])
    (TM2.step (program m)) (.inr 2) (.inr 3) (.inr 4) (.inr 47)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) table [] [] [] [] [] [] [] [] [] [] []) target suffix []
  simpa only [ready,config,tapes3,update_input,update_target,update_temporary,List.append_nil] using h

theorem loop_cons (table target input index output : List Bool) (bit : Bool) :
    TM2.step (program m) (ready m (.inr 4) table target [] [] (bit::input) index [] output) =
      some (ready m (.inr 5) table target [] [] (bit::input) index [] output) := rfl

theorem loop_nil (table target index output : List Bool) :
    TM2.step (program m) (ready m (.inr 4) table target [] [] [] index [] output) =
      some (ready m (.inr 40) table target [] [] [] index [] output) := rfl

theorem parse_endpoint (table target suffix index output : List Bool) (u : ℕ) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 5) table target [] [] (ReachRound.unary u++suffix) index [] output)
      (ready m (.inr 6) table target (List.replicate u true) [] suffix index [] output) (u+1) := by
  have h := UnaryField.exact (inputKey m) (endpointKey m) (by simp [inputKey,endpointKey])
    (TM2.step (program m)) (.inr 5) (.inr 6) (.inr 47) (executesAt_tm2 _ _ _ rfl)
    m.initial (tapes m (fun _ => []) table target [] [] [] [] [] [] index [] [] output) u suffix []
  simpa only [ready,config,UnaryField.tapes,update_input,update_endpoint,List.append_nil] using h

theorem parse_opposite (table target endpoint suffix index output : List Bool) (v : ℕ) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 6) table target endpoint [] (ReachRound.unary v++suffix) index [] output)
      (ready m (.inl (.inr 0)) table target endpoint (List.replicate v true) suffix index [] output) (v+1) := by
  have h := UnaryField.exact (inputKey m) (oppositeKey m) (by simp [inputKey,oppositeKey])
    (TM2.step (program m)) (.inr 6) (.inl (.inr 0)) (.inr 47) (executesAt_tm2 _ _ _ rfl)
    m.initial (tapes m (fun _ => []) table target endpoint [] [] [] [] [] index [] [] output) v suffix []
  simpa only [ready,config,UnaryField.tapes,update_input,update_opposite,List.append_nil] using h

theorem parse_edge (table target suffix index output : List Bool) (u v : ℕ) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 4) table target [] [] (ReachRound.unary u++ReachRound.unary v++suffix) index [] output)
      (ready m (.inl (.inr 0)) table target (List.replicate u true) (List.replicate v true) suffix index [] output)
      (u+v+3) := by
  have nonempty : ∃ bit input, ReachRound.unary u++ReachRound.unary v++suffix = bit::input := by
    cases u with
    | zero => exact ⟨false,ReachRound.unary v++suffix,rfl⟩
    | succ u => exact ⟨true,List.replicate u true++[false]++ReachRound.unary v++suffix,by simp [ReachRound.unary,List.replicate_succ]⟩
  obtain ⟨bit,input,hs⟩ := nonempty
  have a := runsExactly_one (loop_cons m table target input index output bit)
  rw [← hs] at a
  have b := parse_endpoint m table target (ReachRound.unary v++suffix) index output u
  simp only [← List.append_assoc] at b
  have all := (a.trans b).trans (parse_opposite m table target (List.replicate u true) suffix index output v)
  have ht : u+v+3=(v+1)+((u+1)+1) := by omega
  rw [ht]
  exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
