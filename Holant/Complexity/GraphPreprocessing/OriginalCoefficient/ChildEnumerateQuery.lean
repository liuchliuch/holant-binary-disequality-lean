import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumeratePrepare

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem load_row (input edges target index rev output row : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (.inr 7) (fun _ => []) input edges target index row [] [] rev output)
      (config m (.inr 9) (wordTape m.input row) input edges target index [] [] [] rev output) (2*(row.length+1)) := by
  have h := transfer_exact_frame (rowKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [rowKey]) (by simp [rowKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 7) (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) input edges target index [] [] [] rev output) row []
  simpa only [config,tapes3,update_row,update_source,update_temporary,update_empty_source,source_empty,List.append_nil] using h

theorem copy_edges (source : m.K → List Bool) (input edges target index rev output : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (.inr 9) source input edges target index [] [] [] rev output)
      (config m (.inr 11) source input edges target index [] [] edges rev output) (2*(edges.length+1)) := by
  have h := copy_exact_frame (edgesKey m) (copyKey m) (temporaryKey m)
    (by simp [edgesKey,copyKey]) (by simp [edgesKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (.inr 9) (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source input [] target index [] [] [] rev output) edges []
  simpa only [config,tapes3,update_edges,update_copy,update_temporary,List.append_nil] using h

theorem frame_edges (input edges target index rev output payload : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 11) (wordTape m.input payload) input edges target index [] [] edges rev output)
      (config m (.inr 14) (wordTape m.input (Holant.Algebraic.frame edges++payload)) input edges target index [] [] [] rev output)
      (2*edges.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey]) (by simp [copyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 11) (.inr 12) (.inr 13) (.inr 14)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) input edges target index [] [] [] rev output) edges payload
  simpa only [config,tapes3,update_copy,update_source,update_temporary,update_wordTape] using h

theorem copy_target (source : m.K → List Bool) (input edges target index rev output : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (.inr 14) source input edges target index [] [] [] rev output)
      (config m (.inr 16) source input edges target index [] [] target rev output) (2*(target.length+1)) := by
  have h := copy_exact_frame (targetKey m) (copyKey m) (temporaryKey m)
    (by simp [targetKey,copyKey]) (by simp [targetKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (.inr 14) (.inr 15) (.inr 16)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source input edges [] index [] [] [] rev output) target []
  simpa only [config,tapes3,update_target,update_copy,update_temporary,List.append_nil] using h

theorem frame_target (input edges target index rev output payload : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 16) (wordTape m.input payload) input edges target index [] [] target rev output)
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame target++payload)) input edges target index [] [] [] rev output)
      (2*target.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey]) (by simp [copyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 16) (.inr 17) (.inr 18) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) input edges target index [] [] [] rev output) target payload
  simpa only [config,tapes3,update_copy,update_source,update_temporary,update_wordTape] using h

def queryWord (edges target row : List Bool) : List Bool :=
  Holant.Algebraic.frame target++(Holant.Algebraic.frame edges++row)

theorem prepare_query (input edges target index rev output row : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 7) (fun _ => []) input edges target index row [] [] rev output)
      (config m (.inl m.main) (wordTape m.input (queryWord edges target row)) input edges target index [] [] [] rev output)
      (2*row.length+4*edges.length+4*target.length+12) := by
  have all := ((((load_row m input edges target index rev output row).trans
    (copy_edges m (wordTape m.input row) input edges target index rev output)).trans
    (frame_edges m input edges target index rev output row)).trans
    (copy_target m (wordTape m.input (Holant.Algebraic.frame edges++row)) input edges target index rev output)).trans
    (frame_target m input edges target index rev output (Holant.Algebraic.frame edges++row))
  have ht : 2*row.length+4*edges.length+4*target.length+12 =
      (2*target.length+3)+(2*(target.length+1)+((2*edges.length+3)+(2*(edges.length+1)+2*(row.length+1)))) := by omega
  rw [ht]; exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
