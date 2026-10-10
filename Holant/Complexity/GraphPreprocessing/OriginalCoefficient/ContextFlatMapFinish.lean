import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapStages

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

theorem tag_nil (context rev out : List Bool) :
    TM2.step (program m) (ready m (.inr 2) [false] context rev out)=some (ready m (.inr 9) [] context rev out) := by
  change some (cfg (.inr 9 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) [false] context [] [] rev out) (inputKey m) []))=_
  rw [update_input]; rfl
theorem eof (context rev out : List Bool) :
    TM2.step (program m) (ready m (.inr 9) [] context rev out)=some (ready m (.inr 12) [] context rev out) := by
  change some (cfg (.inr 12 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) [] context [] [] rev out) (inputKey m) []))=_
  rw [update_input]; rfl
theorem trailing_reject (context rev out : List Bool) (bit : Bool) (tail : List Bool) :
    TM2.step (program m) (ready m (.inr 9) (bit::tail) context rev out)=
      some (ready m (.inr 15) tail context rev out) := by
  change some (cfg (.inr 15 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) (bit::tail) context [] [] rev out) (inputKey m) tail))=_
  rw [update_input]; rfl
theorem reject_halts (work : Stack m → List Bool) :
    TM2.step (program m) (cfg (.inr 15) m.initial work)=
      some (⟨none,(some false,m.initial),work⟩ : (machine m).Config) := rfl

theorem clear_context (context rev out : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 12) [] context rev out)
      (ready m (.inr 13) [] [] rev out) (context.length+1) := by
  have h := clear_exact (TM2.step (program m)) (contextKey m) (.inr 12) (.inr 13)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) [] context [] [] rev out)
  rw [update_context] at h
  change RunsExactly _ _ _ (context.length+1) at h
  exact h
theorem reverse_output (rev out : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 13) [] [] rev out)
      (ready m (.inr 14) [] [] [] (rev.reverse++out)) (rev.length+1) := by
  have h := copy_move_exact (reverseKey m) (copyKey m) (outputKey m)
    (by simp [reverseKey,copyKey]) (by simp [reverseKey,outputKey])
    (TM2.step (program m)) (.inr 13) (.inr 14) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] []) rev [] out
  simpa only [ready,config,tapes3,update_rev,update_copied,update_output] using h
theorem halt_step (out : List Bool) :
    TM2.step (program m) (ready m (.inr 14) [] [] [] out)=some (haltList (machine m).computer out) := by
  rw [Machine.halt_eq]
  have hw := update_output m (fun _ => []) [] [] [] [] [] [] out
  rw [tapes_empty] at hw
  change wordTape (outputKey m) out=_ at hw
  change some (⟨none,(none,m.initial),tapes m (fun _ => []) [] [] [] [] [] out⟩ : (machine m).Config)=_
  rw [←hw]
theorem finish (context rev : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 2) [false] context rev [])
      (haltList (machine m).computer rev.reverse) (context.length+rev.length+5) := by
  have all := ((((runsExactly_one (tag_nil m context rev [])).trans (runsExactly_one (eof m context rev []))).trans
    (clear_context m context rev [])).trans (reverse_output m rev [])).trans
    (runsExactly_one (halt_step m (rev.reverse++[])))
  simp only [List.append_nil] at all
  have ht : context.length+rev.length+5=1+((rev.length+1)+((context.length+1)+(1+1))) := by omega
  rw [ht]
  exact all
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMap
