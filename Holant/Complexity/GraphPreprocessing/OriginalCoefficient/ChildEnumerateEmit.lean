import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateCall

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

def childEntry (n : ℕ) : List Bool := true::Holant.Algebraic.frame (List.replicate n true)
theorem frame_unary (n : ℕ) : Holant.Algebraic.frame (List.replicate n true)=List.replicate (2*n) true++[false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,Holant.Algebraic.frame,ih,Nat.mul_succ]
theorem childEntry_reverse (n : ℕ) : (childEntry n).reverse=false::List.replicate (2*n+1) true := by
  simp only [childEntry,frame_unary,List.reverse_cons,List.reverse_append,List.reverse_singleton,List.reverse_replicate,List.reverse_nil,List.nil_append,List.cons_append,List.append_assoc]
  rw [←List.replicate_succ']

theorem seed_entry (input edges target index rev output : List Bool) :
    TM2.step (program m) (ready m (.inr 20) input edges target index rev output) =
      some (ready m (.inr 21) input edges target index (true::rev) output) := by
  change some (cfg (.inr 21 : Label m) m.initial (Function.update
    (tapes m (fun _ => []) input edges target index [] [] [] rev output) (reverseKey m) (true::rev))) = _
  rw [update_rev]; rfl

theorem copy_index (input edges target index rev output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 21) input edges target index rev output)
      (config m (.inr 23) (fun _ => []) input edges target index [] [] index rev output) (2*(index.length+1)) := by
  have h := copy_exact_frame (indexKey m) (copyKey m) (temporaryKey m)
    (by simp [indexKey,copyKey]) (by simp [indexKey,temporaryKey]) (by simp [copyKey,temporaryKey])
    (TM2.step (program m)) (.inr 21) (.inr 22) (.inr 23)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) input edges target [] [] [] [] rev output) index []
  simpa only [ready,config,tapes3,update_index,update_copy,update_temporary,List.append_nil] using h

theorem emit_cons (input edges target index copy rev output : List Bool) :
    TM2.step (program m) (config m (.inr 23) (fun _ => []) input edges target index [] [] (true::copy) rev output) =
      some (config m (.inr 23) (fun _ => []) input edges target index [] [] copy (true::true::rev) output) := by
  change some (cfg (.inr 23 : Label m) m.initial (Function.update (Function.update (Function.update
    (tapes m (fun _ => []) input edges target index [] [] (true::copy) rev output) (copyKey m) copy)
      (reverseKey m) (true::rev)) (reverseKey m) (true::true::rev))) = _
  rw [update_copy,update_rev,update_rev]; rfl

theorem emit_nil (input edges target index rev output : List Bool) :
    TM2.step (program m) (config m (.inr 23) (fun _ => []) input edges target index [] [] [] rev output) =
      some (ready m (.inr 25) input edges target index (false::rev) output) := by
  change some (cfg (.inr 25 : Label m) m.initial (Function.update (Function.update
    (tapes m (fun _ => []) input edges target index [] [] [] rev output) (copyKey m) []) (reverseKey m) (false::rev))) = _
  rw [update_copy,update_rev]; rfl

theorem emit_loop (n : ℕ) (input edges target index rev output : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 23) (fun _ => []) input edges target index [] [] (List.replicate n true) rev output)
      (ready m (.inr 25) input edges target index (false::(List.replicate (2*n) true++rev)) output) (n+1) := by
  induction n generalizing rev with
  | zero => simpa using runsExactly_one (emit_nil m input edges target index rev output)
  | succ n ih =>
    have h := (runsExactly_one (emit_cons m input edges target index (List.replicate n true) rev output)).trans (ih (true::true::rev))
    have hw : List.replicate (2*n) true++true::true::rev = List.replicate (2*(n+1)) true++rev := by
      calc
        _ = (List.replicate (2*n) true++List.replicate 2 true)++rev := by simp
        _ = List.replicate (2*n+2) true++rev := by rw [←List.replicate_add]
        _ = _ := by congr 2
    simpa only [List.replicate_succ,hw,Nat.add_assoc] using h

theorem emit_index (n : ℕ) (input edges target rev output : List Bool) :
    RunsExactly (TM2.step (program m)) (ready m (.inr 20) input edges target (List.replicate n true) rev output)
      (ready m (.inr 25) input edges target (List.replicate n true) ((childEntry n).reverse++rev) output) (3*n+4) := by
  have all := ((runsExactly_one (seed_entry m input edges target (List.replicate n true) rev output)).trans
    (copy_index m input edges target (List.replicate n true) (true::rev) output)).trans
    (emit_loop m n input edges target (List.replicate n true) (true::rev) output)
  have hw : false::(List.replicate (2*n) true++true::rev)=(childEntry n).reverse++rev := by
    rw [childEntry_reverse]
    simp only [List.cons_append]
    rw [List.replicate_succ']
    simp
  have ht : 3*n+4=(n+1)+(2*((List.replicate n true).length+1)+1) := by simp; omega
  rw [ht]
  simpa only [hw] using all

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
