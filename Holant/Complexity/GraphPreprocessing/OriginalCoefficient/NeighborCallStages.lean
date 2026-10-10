import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCallTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem copy_opposite (table target endpoint opposite suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 0) (wordTape m.input suffix) table target endpoint opposite [] [] [])
      (config m (.inr 2) (wordTape m.input (opposite++suffix)) table target endpoint opposite [] [] [])
      (2*(opposite.length+1)) := by
  have h := copy_exact_frame (oppositeKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [oppositeKey]) (by simp [oppositeKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 0) (.inr 1) (.inr 2)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table target endpoint [] [] [] []) opposite suffix
  simpa only [config,tapes3,update_opposite,update_source,update_temporary,update_wordTape] using h

theorem copy_table (source : m.K → List Bool) (table target endpoint opposite : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 2) source table target endpoint opposite [] [] [])
      (config m (.inr 4) source table target endpoint opposite [] table []) (2*(table.length+1)) := by
  have h := copy_exact_frame (tableKey m) (copyKey m) (temporaryKey m)
    (by simp [tableKey,copyKey]) (by simp [tableKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (.inr 2) (.inr 3) (.inr 4)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source [] target endpoint opposite [] [] []) table []
  simpa only [config,tapes3,update_table,update_copy,update_temporary,List.append_nil] using h

theorem frame_table (table target endpoint opposite suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 4) (wordTape m.input suffix) table target endpoint opposite [] table [])
      (config m (.inr 7) (wordTape m.input (Holant.Algebraic.frame table++suffix)) table target endpoint opposite [] [] [])
      (2*table.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey]) (by simp [copyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 4) (.inr 5) (.inr 6) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table target endpoint opposite [] [] []) table suffix
  simpa only [config,tapes3,update_copy,update_source,update_temporary,update_wordTape] using h

theorem copy_endpoint (source : m.K → List Bool) (table target endpoint opposite : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 7) source table target endpoint opposite [] [] [])
      (config m (.inr 9) source table target endpoint opposite [] [] endpoint) (2*(endpoint.length+1)) := by
  have h := copy_exact_frame (endpointKey m) (comparisonKey m) (temporaryKey m)
    (by simp [endpointKey,comparisonKey]) (by simp [endpointKey,temporaryKey]) (by simp [comparisonKey,temporaryKey])
    (TM2.step (program m)) (.inr 7) (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source table target [] opposite [] [] []) endpoint []
  simpa only [config,tapes3,update_endpoint,update_comparison,update_temporary,List.append_nil] using h

theorem copy_target (source : m.K → List Bool) (table target endpoint opposite comparison : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 9) source table target endpoint opposite [] [] comparison)
      (config m (.inr 11) source table target endpoint opposite [] target comparison) (2*(target.length+1)) := by
  have h := copy_exact_frame (targetKey m) (copyKey m) (temporaryKey m)
    (by simp [targetKey,copyKey]) (by simp [targetKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (.inr 9) (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source table [] endpoint opposite [] [] comparison) target []
  simpa only [config,tapes3,update_target,update_copy,update_temporary,List.append_nil] using h

theorem frame_target (source : m.K → List Bool) (table target endpoint opposite comparison : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 11) source table target endpoint opposite [] target comparison)
      (config m (.inr 14) source table target endpoint opposite [] [] (Holant.Algebraic.frame target++comparison))
      (2*target.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (comparisonKey m) (temporaryKey m)
    (by simp [copyKey,comparisonKey]) (by simp [copyKey,temporaryKey]) (by simp [comparisonKey,temporaryKey])
    (TM2.step (program m)) (.inr 11) (.inr 12) (.inr 13) (.inr 14)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m source table target endpoint opposite [] [] []) target comparison
  simpa only [config,tapes3,update_copy,update_comparison,update_temporary] using h

theorem frame_comparison (table target endpoint opposite comparison suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 14) (wordTape m.input suffix) table target endpoint opposite [] [] comparison)
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame comparison++suffix)) table target endpoint opposite [] [] [])
      (2*comparison.length+3) := by
  have h := FrameEmit.prepend_exact (comparisonKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [comparisonKey]) (by simp [comparisonKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 14) (.inr 15) (.inr 16) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) table target endpoint opposite [] [] []) comparison suffix
  simpa only [config,tapes3,update_comparison,update_source,update_temporary,update_wordTape] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCall
