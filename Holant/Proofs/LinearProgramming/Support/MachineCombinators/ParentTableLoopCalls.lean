import Holant.Proofs.LinearProgramming.Support.MachineCombinators.ParentTableLoopControl

open Holant.Complexity Holant.Complexity.GraphPreprocessing
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.ParentTableLoop
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- The provider's actual transitions run with the entire caller frame retained. -/
theorem call_row (raw index output vertices result : List Bool) (n : ℕ)
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

def entry (result : List Bool) : List Bool := true::Holant.Algebraic.frame result

/-- A real frame emitter consumes the provider output and prepends one row,
without traversing the already accumulated list suffix. -/
theorem emit_row (raw index output vertices result : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 14) (wordTape m.output result) raw index output [] [] vertices [])
      (cleanConfig m (.inr 6) raw index (entry result++output) vertices []) (2*result.length+4) := by
  have run := FrameEmit.prepend_exact (Sum.inl m.output : Stack m) (outputKey m) (temporaryKey m)
    (by simp [outputKey]) (by simp [temporaryKey]) (by simp [outputKey,temporaryKey])
    (TM2.step (program m)) (.inr 14) (.inr 15) (.inr 16) (.inr 17)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output []) raw index [] [] [] vertices []) result output
  simp only [tapes3,update_source,update_output,update_temporary,update_wordTape,source_empty,update_empty_source] at run
  have mark : TM2.step (program m)
      (cleanConfig m (.inr 17) raw index (Holant.Algebraic.frame result++output) vertices []) =
        some (cleanConfig m (.inr 6) raw index (entry result++output) vertices []) := by
    change some (cfg (.inr 6 : Label m) m.initial (Function.update
      (tapes m (fun _ => []) raw index (Holant.Algebraic.frame result++output) [] [] vertices []) (outputKey m)
      (true::(Holant.Algebraic.frame result++output)))) = _
    rw [update_output]; rfl
  have ht : 2*result.length+4=1+(2*result.length+3) := by omega
  rw [ht]
  exact run.trans (runsExactly_one mark)

/-- One genuine descending-counter iteration. The counter is preserved after
its initial pop, and every source call, copy, delimiter and EOF is charged. -/
theorem round_exact (raw index output vertices result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n]
      (some (initList m.computer (Holant.Algebraic.frame raw ++ index))) = some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (cleanConfig m (.inr 6) raw (true::index) output vertices [])
      (cleanConfig m (.inr 6) raw index (entry result++output) vertices [])
      (n+4*raw.length+2*index.length+2*result.length+12) := by
  have all := (((((runsExactly_one (loop_cons m raw index output vertices true)).trans
    (copy_index m raw index output vertices)).trans (copy_raw m raw index output vertices)).trans
    (frame_query m raw index output vertices)).trans (call_row m raw index output vertices result n h)).trans
    (emit_row m raw index output vertices result)
  have ht : n+4*raw.length+2*index.length+2*result.length+12 =
      (2*result.length+4)+(n+(2*raw.length+3+(2*(raw.length+1)+(2*(index.length+1)+1)))) := by omega
  rw [ht]
  exact all

end Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.ParentTableLoop
