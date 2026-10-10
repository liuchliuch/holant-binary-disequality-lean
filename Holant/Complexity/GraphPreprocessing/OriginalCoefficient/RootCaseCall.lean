import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborCallTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem load_input (input : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (phase m 3) input [] [])
      (config m (.inl m.main) (wordTape m.input input) [] [] []) (2*(input.length+1)) := by
  have h := transfer_exact_frame (inputKey m) (Sum.inl m.input : Stack m) (temporaryKey m)
    (by simp [inputKey]) (by simp [inputKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (phase m 3) (phase m 4) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] []) input []
  simpa only [ready,config,tapes3,update_input,update_source,update_temporary,
    NeighborCall.update_empty_source,NeighborCall.source_empty,List.append_nil] using h

theorem call_provider (input output : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer input)) = some (haltList m.computer output)) :
    RunsExactly (TM2.step (program m)) (config m (.inl m.main) (wordTape m.input input) [] [] [])
      (config m (phase m 5) (wordTape m.output output) [] [] []) n := by
  let frame := extras [] [] []
  have run := Call.run (LeftMap.states m) Sum.inl (some (phase m 5)) m.program (program m)
    (fun _ => rfl) (initList m.computer input) (haltList m.computer output) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (phase m 5)) (initList m.computer input) =
      config m (.inl m.main) (wordTape m.input input) [] [] [] := by rw [Machine.init_eq]; rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (phase m 5)) (haltList m.computer output) =
      config m (phase m 5) (wordTape m.output output) [] [] [] := by rw [Machine.halt_eq]; rfl
  rw [hi,ho] at run
  exact run

theorem return_output (output : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (phase m 5) (wordTape m.output output) [] [] [])
      (ready m (phase m 7) [] [] output) (2*(output.length+1)) := by
  have h := transfer_exact_frame (Sum.inl m.output : Stack m) (outputKey m) (temporaryKey m)
    (by simp [outputKey]) (by simp [temporaryKey]) (by simp [outputKey,temporaryKey])
    (TM2.step (program m)) (phase m 5) (phase m 6) (phase m 7)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output []) [] [] []) output []
  simpa only [ready,config,tapes3,update_source,update_output,update_temporary,
    NeighborCall.update_wordTape,NeighborCall.update_empty_source,NeighborCall.source_empty,List.append_nil] using h

theorem nonroot_exact (input output : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer input)) = some (haltList m.computer output)) :
    RunsExactly (machine m).computer.step
      (initList (machine m).computer (Holant.Algebraic.frame [false]++input))
      (haltList (machine m).computer output) (n+2*input.length+2*output.length+10) := by
  have all := (((((parse_flag m false input).trans (runsExactly_one (read_flag m false input))).trans
    (load_input m input)).trans (call_provider m input output n h)).trans
    (return_output m output)).trans (runsExactly_one (halt_step m output))
  rw [initial]
  change RunsExactly (TM2.step (program m)) _ _ _
  convert all using 1 <;> omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCase
