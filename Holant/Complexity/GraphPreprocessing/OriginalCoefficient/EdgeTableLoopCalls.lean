import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoopControl

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- The provider's actual transitions run with the entire caller frame retained. -/
theorem call_edge (raw index output vertices result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n]
      (some (initList m.computer (Holant.Algebraic.frame raw ++ index))) = some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame raw ++ index)) raw index output [] [] vertices [])
      (config m (.inr 14) (wordTape m.output result) raw index output [] [] vertices []) n := by
  let frame := extras raw index output [] [] vertices []
  have run := Call.run (LeftMap.states m) Sum.inl (some (.inr (14 : Fin 24))) m.program (program m)
    (fun _ => rfl) (initList m.computer (Holant.Algebraic.frame raw ++ index))
      (haltList m.computer result) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (14 : Fin 24)))
      (initList m.computer (Holant.Algebraic.frame raw ++ index)) =
      config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame raw ++ index)) raw index output [] [] vertices [] := by
    rw [Machine.init_eq]
    rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (14 : Fin 24)))
      (haltList m.computer result) =
      config m (.inr 14) (wordTape m.output result) raw index output [] [] vertices [] := by
    rw [Machine.halt_eq]
    rfl
  rw [hi,ho] at run
  exact run

/-- Moving the returned edge word prepends it without traversing the already
accumulated table suffix. The provider's final output tape is cleared too. -/
theorem emit_edge (raw index output vertices result : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 14) (wordTape m.output result) raw index output [] [] vertices [])
      (cleanConfig m (.inr 6) raw index (result++output) vertices []) (2*(result.length+1)) := by
  have run := transfer_exact_frame (Sum.inl m.output : Stack m) (outputKey m) (temporaryKey m)
    (by simp [outputKey]) (by simp [temporaryKey]) (by simp [outputKey,temporaryKey])
    (TM2.step (program m)) (.inr 14) (.inr 15) (.inr 6)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output []) raw index [] [] [] vertices []) result output
  simpa only [cleanConfig,config,tapes3,update_source,update_output,update_temporary,update_wordTape,source_empty,update_empty_source] using run

/-- One genuine descending-counter iteration. The counter is preserved after
its initial pop, and every source call, copy, delimiter and EOF is charged. -/
theorem round_exact (raw index output vertices result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n]
      (some (initList m.computer (Holant.Algebraic.frame raw ++ index))) = some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (cleanConfig m (.inr 6) raw (true::index) output vertices [])
      (cleanConfig m (.inr 6) raw index (result++output) vertices [])
      (n+4*raw.length+2*index.length+2*result.length+10) := by
  have all := (((((runsExactly_one (loop_cons m raw index output vertices true)).trans
    (copy_index m raw index output vertices)).trans (copy_raw m raw index output vertices)).trans
    (frame_query m raw index output vertices)).trans (call_edge m raw index output vertices result n h)).trans
    (emit_edge m raw index output vertices result)
  have ht : n+4*raw.length+2*index.length+2*result.length+10 =
      2*(result.length+1)+(n+(2*raw.length+3+(2*(raw.length+1)+(2*(index.length+1)+1)))) := by omega
  rw [ht]
  exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeTableLoop
