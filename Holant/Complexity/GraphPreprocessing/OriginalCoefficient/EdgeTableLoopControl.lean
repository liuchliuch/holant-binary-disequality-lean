import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoopTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

theorem parse_raw (raw suffix : List Bool) :
    RunsExactly (TM2.step (program m))
      (cleanConfig m (.inr 0) [] [] [] [] (Holant.Algebraic.frame raw ++ suffix))
      (cleanConfig m (.inr 2) raw [] [] [] suffix) (2*(raw.length+1)) := by
  have run := Frame.extract_exact (inputKey m) (rawKey m) (temporaryKey m)
    (by simp [inputKey,rawKey]) (by simp [inputKey,temporaryKey]) (by simp [rawKey,temporaryKey])
    (TM2.step (program m)) (.inr 0) (.inr 1) (.inr 2) (.inr 23)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] []) raw suffix []
  simpa only [cleanConfig,config,tapes3,update_input,update_raw,update_temporary,List.append_nil] using run

theorem parse_vertices (raw vertices index : List Bool) :
    RunsExactly (TM2.step (program m))
      (cleanConfig m (.inr 2) raw [] [] [] (Holant.Algebraic.frame vertices ++ index))
      (cleanConfig m (.inr 4) raw [] [] vertices index) (2*(vertices.length+1)) := by
  have run := Frame.extract_exact (inputKey m) (verticesKey m) (temporaryKey m)
    (by simp [inputKey,verticesKey]) (by simp [inputKey,temporaryKey]) (by simp [verticesKey,temporaryKey])
    (TM2.step (program m)) (.inr 2) (.inr 3) (.inr 4) (.inr 23)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) raw [] [] [] [] [] []) vertices index []
  simpa only [cleanConfig,config,tapes3,update_input,update_vertices,update_temporary,List.append_nil] using run

theorem move_index (raw vertices index : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 4) raw [] [] vertices index)
      (cleanConfig m (.inr 6) raw index [] vertices []) (2*(index.length+1)) := by
  have run := transfer_exact_frame (inputKey m) (indexKey m) (temporaryKey m)
    (by simp [inputKey,indexKey]) (by simp [inputKey,temporaryKey]) (by simp [indexKey,temporaryKey])
    (TM2.step (program m)) (.inr 4) (.inr 5) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) raw [] [] [] [] vertices []) index []
  simpa only [cleanConfig,config,tapes3,update_input,update_index,update_temporary,List.append_nil] using run

theorem enter_loop (raw vertices index : List Bool) :
    RunsExactly (TM2.step (program m))
      (cleanConfig m (.inr 0) [] [] [] [] (Holant.Algebraic.frame raw ++ (Holant.Algebraic.frame vertices ++ index)))
      (cleanConfig m (.inr 6) raw index [] vertices [])
      (2*raw.length+2*vertices.length+2*index.length+6) := by
  have all := ((parse_raw m raw (Holant.Algebraic.frame vertices ++ index)).trans
    (parse_vertices m raw vertices index)).trans (move_index m raw vertices index)
  have ht : 2*raw.length+2*vertices.length+2*index.length+6 =
      2*(index.length+1)+(2*(vertices.length+1)+2*(raw.length+1)) := by omega
  rw [ht]
  exact all

theorem loop_cons (raw index output vertices : List Bool) (bit : Bool) :
    TM2.step (program m) (cleanConfig m (.inr 6) raw (bit::index) output vertices []) =
      some (cleanConfig m (.inr 7) raw index output vertices []) := by
  change some (cfg (.inr 7 : Label m) m.initial
    (Function.update (tapes m (fun _ => []) raw (bit::index) output [] [] vertices []) (indexKey m) index)) = _
  rw [update_index]
  rfl

theorem loop_nil (raw output vertices : List Bool) :
    TM2.step (program m) (cleanConfig m (.inr 6) raw [] output vertices []) =
      some (cleanConfig m (.inr 18) raw [] output vertices []) := by
  change some (cfg (.inr 18 : Label m) m.initial
    (Function.update (tapes m (fun _ => []) raw [] output [] [] vertices []) (indexKey m) [])) = _
  rw [update_index]
  rfl

/-- Both the raw graph and remaining original unary index stay on caller tapes. -/
theorem copy_index (raw index output vertices : List Bool) :
    RunsExactly (TM2.step (program m)) (cleanConfig m (.inr 7) raw index output vertices [])
      (config m (.inr 9) (wordTape m.input index) raw index output [] [] vertices []) (2*(index.length+1)) := by
  have run := copy_exact_frame (indexKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [indexKey]) (by simp [indexKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 7) (.inr 8) (.inr 9)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) raw [] output [] [] vertices []) index []
  simpa only [cleanConfig,config,tapes3,update_index,update_source,update_temporary,update_wordTape,
    source_empty,update_empty_source,List.append_nil] using run

theorem copy_raw (raw index output vertices : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 9) (wordTape m.input index) raw index output [] [] vertices [])
      (config m (.inr 11) (wordTape m.input index) raw index output [] raw vertices []) (2*(raw.length+1)) := by
  have run := copy_exact_frame (rawKey m) (rawCopyKey m) (temporaryKey m)
    (by simp [rawKey,rawCopyKey]) (by simp [rawKey,temporaryKey]) (by simp [rawCopyKey,temporaryKey])
    (TM2.step (program m)) (.inr 9) (.inr 10) (.inr 11)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input index) [] index output [] [] vertices []) raw []
  simpa only [config,tapes3,update_raw,update_rawCopy,update_temporary,List.append_nil] using run

/-- Real frame emission constructs the provider's unchanged raw/index codec. -/
theorem frame_query (raw index output vertices : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 11) (wordTape m.input index) raw index output [] raw vertices [])
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame raw ++ index))
        raw index output [] [] vertices []) (2*raw.length+3) := by
  have run := FrameEmit.prepend_exact (rawCopyKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [rawCopyKey]) (by simp [rawCopyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 11) (.inr 12) (.inr 13) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) raw index output [] [] vertices []) raw index
  simpa only [config,tapes3,update_rawCopy,update_source,update_temporary,update_wordTape] using run

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
