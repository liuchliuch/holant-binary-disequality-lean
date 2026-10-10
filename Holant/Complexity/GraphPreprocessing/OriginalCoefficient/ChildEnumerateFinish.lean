import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateEmit

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem match_exact (input edges target rev output row : List Bool) (i n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer (queryWord edges target row))) =
      some (haltList m.computer [true])) :
    RunsExactly (TM2.step (program m))
      (ready m (.inr 4) (true::(Holant.Algebraic.frame row++input)) edges target (List.replicate i true) rev output)
      (ready m (.inr 4) input edges target (List.replicate (i+1) true) ((childEntry i).reverse++rev) output)
      (n+4*row.length+4*edges.length+4*target.length+3*i+21) := by
  have all := ((read_row m input edges target (List.replicate i true) rev output row true n h).trans
    (emit_index m i input edges target rev output)).trans
    (runsExactly_one (advance m input edges target (List.replicate i true) ((childEntry i).reverse++rev) output))
  have ht : n+4*row.length+4*edges.length+4*target.length+3*i+21 =
      1+((3*i+4)+(n+4*row.length+4*edges.length+4*target.length+16)) := by omega
  rw [ht]
  simpa only [List.replicate_succ] using all

theorem clear_context (edges target index rev : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 30) [] edges target index rev [])
      (ready m (.inr 33) [] [] [] [] rev []) (edges.length+target.length+index.length+3) := by
  have a := clear_exact (TM2.step (program m)) (edgesKey m) (.inr 30) (.inr 31)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) [] edges target index [] [] [] rev [])
  rw [update_edges] at a
  change RunsExactly (TM2.step (program m)) _ _ (edges.length+1) at a
  have b := clear_exact (TM2.step (program m)) (targetKey m) (.inr 31) (.inr 32)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) [] [] target index [] [] [] rev [])
  rw [update_target] at b
  change RunsExactly (TM2.step (program m)) _ _ (target.length+1) at b
  have c := clear_exact (TM2.step (program m)) (indexKey m) (.inr 32) (.inr 33)
    (executesAt_tm2 _ _ _ rfl) m.initial (tapes m (fun _ => []) [] [] [] index [] [] [] rev [])
  rw [update_index] at c
  change RunsExactly (TM2.step (program m)) _ _ (index.length+1) at c
  have ht : edges.length+target.length+index.length+3=(index.length+1)+((target.length+1)+(edges.length+1)) := by omega
  rw [ht]; exact (a.trans b).trans c

theorem seed_nil (rev : List Bool) :
    TM2.step (program m) (ready m (.inr 33) [] [] [] [] rev []) =
      some (ready m (.inr 34) [] [] [] [] (false::rev) []) := by
  change some (cfg (.inr 34 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) [] [] [] [] [] [] [] rev []) (reverseKey m) (false::rev))) = _
  rw [update_rev]; rfl

theorem reverse_output (rev : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 34) [] [] [] [] (false::rev) [])
      (ready m (.inr 35) [] [] [] [] [] (rev.reverse++[false])) (rev.length+2) := by
  have h := copy_move_exact (reverseKey m) (copyKey m) (outputKey m)
    (by simp [reverseKey,copyKey]) (by simp [reverseKey,outputKey])
    (TM2.step (program m)) (.inr 34) (.inr 35) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] [] [] [] [] [] [] []) (false::rev) [] []
  simpa only [ready,config,tapes3,update_rev,update_copy,update_output,List.reverse_cons,List.append_nil,List.length_cons,Nat.add_assoc] using h

theorem halt_step (output : List Bool) :
    TM2.step (program m) (ready m (.inr 35) [] [] [] [] [] output) =
      some (haltList (machine m).computer output) := by
  rw [Machine.halt_eq]
  have hw := update_output m (fun _ => []) [] [] [] [] [] [] [] [] [] output
  rw [tapes_empty] at hw
  change wordTape (outputKey m) output = _ at hw
  change some (⟨none,(none,m.initial),Function.update
    (tapes m (fun _ => []) [] [] [] [] [] [] [] [] output) (inputKey m) []⟩ : (machine m).Config) = _
  rw [update_input,←hw]

theorem finish (edges target index rev : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 30) [] edges target index rev [])
      (haltList (machine m).computer (rev.reverse++[false]))
      (edges.length+target.length+index.length+rev.length+7) := by
  have all := (((clear_context m edges target index rev).trans (runsExactly_one (seed_nil m rev))).trans
    (reverse_output m rev)).trans (runsExactly_one (halt_step m (rev.reverse++[false])))
  have ht : edges.length+target.length+index.length+rev.length+7 =
      1+((rev.length+2)+(1+(edges.length+target.length+index.length+3))) := by omega
  rw [ht]; exact all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
