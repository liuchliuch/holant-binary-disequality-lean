import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapTapes

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem prepare (context input : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 0) (Holant.Algebraic.frame context++input) [] [] [])
      (ready m (.inr 2) input context [] []) (2*(context.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (contextKey m) (temporaryKey m)
    (by simp [inputKey,contextKey]) (by simp [inputKey,temporaryKey]) (by simp [contextKey,temporaryKey])
    (TM2.step (program m)) (.inr 0) (.inr 1) (.inr 2) (.inr 15)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] []) context input []
  simpa only [ready,config,tapes3,update_input,update_context,update_temporary,List.append_nil] using h

theorem tag_cons (context input rev out : List Bool) :
    TM2.step (program m) (ready m (.inr 2) (true::input) context rev out)=
      some (ready m (.inr 3) input context rev out) := by
  change some (cfg (.inr 3 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) (true::input) context [] [] rev out) (inputKey m) input))=_
  rw [update_input]
  rfl

theorem extract_entry (context input rev out word : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 3) (Holant.Algebraic.frame word++input) context rev out)
      (config m (.inr 5) (wordTape m.input word) input context [] [] rev out) (2*(word.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (.inl m.input : Stack m) (temporaryKey m)
    (by simp [inputKey]) (by simp [inputKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 3) (.inr 4) (.inr 5) (.inr 15)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] context [] [] rev out) word input []
  simpa only [ready,config,tapes3,update_input,update_source,update_temporary,update_empty_source,source_empty,List.append_nil] using h

theorem copy_context (context input rev out word : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (.inr 5) (wordTape m.input word) input context [] [] rev out)
      (config m (.inr 7) (wordTape m.input word) input context [] context rev out) (2*(context.length+1)) := by
  have h := copy_exact_frame (contextKey m) (copyKey m) (temporaryKey m)
    (by simp [contextKey,copyKey]) (by simp [contextKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (.inr 5) (.inr 6) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input word) input [] [] [] rev out) context []
  simpa only [config,tapes3,update_context,update_copied,update_temporary,List.append_nil] using h

theorem frame_context (context input rev out word : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (.inr 7) (wordTape m.input word) input context [] context rev out)
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame context++word)) input context [] [] rev out)
      (2*context.length+3) := by
  have h := FrameEmit.prepend_exact (copyKey m) (.inl m.input : Stack m) (temporaryKey m)
    (by simp [copyKey]) (by simp [copyKey,temporaryKey]) (by simp [temporaryKey])
    (TM2.step (program m)) (.inr 7) (.inr 8) (.inr 10) (.inl m.main)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.input []) input context [] [] rev out) context word
  simpa only [config,tapes3,update_copied,update_source,update_wordTape,update_temporary] using h

theorem call (context input rev out word result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (Holant.Algebraic.frame context++word)))=
      some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame context++word)) input context [] [] rev out)
      (config m (.inr 11) (wordTape m.output result) input context [] [] rev out) n := by
  let frame := extras input context [] [] rev out
  have hrun := Call.run (LeftMap.states m) Sum.inl (some (.inr (11 : Fin 16))) m.program (program m)
    (fun _ => rfl) (initList m.computer (Holant.Algebraic.frame context++word)) (haltList m.computer result) frame n h
  have hi : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (11 : Fin 16)))
      (initList m.computer (Holant.Algebraic.frame context++word)) =
      config m (.inl m.main) (wordTape m.input (Holant.Algebraic.frame context++word)) input context [] [] rev out := by
    rw [Machine.init_eq]; rfl
  have ho : embedCfg (Returning.layout frame) (LeftMap.states m) Sum.inl (some (.inr (11 : Fin 16)))
      (haltList m.computer result)=config m (.inr 11) (wordTape m.output result) input context [] [] rev out := by
    rw [Machine.halt_eq]; rfl
  rw [hi,ho] at hrun
  exact hrun

theorem emit (context input rev out result : List Bool) :
    RunsExactly (TM2.step (program m)) (config m (.inr 11) (wordTape m.output result) input context [] [] rev out)
      (ready m (.inr 2) input context (result.reverse++rev) out) (result.length+1) := by
  have h := copy_move_exact (.inl m.output : Stack m) (copyKey m) (reverseKey m)
    (by simp [copyKey]) (by simp [reverseKey])
    (TM2.step (program m)) (.inr 11) (.inr 2) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (wordTape m.output []) input context [] [] [] out) result [] rev
  simpa only [ready,config,tapes3,update_source,update_wordTape,update_copied,update_rev,source_empty,update_empty_source] using h

theorem round (context input rev out word result : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (Holant.Algebraic.frame context++word)))=
      some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 2) (true::(Holant.Algebraic.frame word++input)) context rev out)
      (ready m (.inr 2) input context (result.reverse++rev) out)
      (n+4*context.length+2*word.length+result.length+9) := by
  have all := (((((runsExactly_one (tag_cons m context (Holant.Algebraic.frame word++input) rev out)).trans
    (extract_entry m context input rev out word)).trans (copy_context m context input rev out word)).trans
    (frame_context m context input rev out word)).trans (call m context input rev out word result n h)).trans
    (emit m context input rev out result)
  have ht : n+4*context.length+2*word.length+result.length+9=
      (result.length+1)+(n+((2*context.length+3)+(2*(context.length+1)+(2*(word.length+1)+1)))) := by omega
  rw [ht]
  exact all
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
