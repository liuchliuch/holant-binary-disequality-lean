import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.GraphCodeMachine
open Components (active base tapes)
variable {A : Type} (e : Encoding A Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option Elab.async false

def listTicks (ds : List (Code A)) : ℕ := (ds.map (entryTicks e)).sum


/-- Complete streaming loop with an arbitrary retained suffix and accumulated bits. -/
theorem list_exact (ds : List (Code A)) (suffix output : List Bool) (n : ℕ) :
    RunsExactly (driver e).computer.step
      (active (identityMachine) 0
        (records (entryEncoding e) ds ++ suffix) [] output (List.replicate n true))
      (active (identityMachine) 0 suffix []
        ((chunk e (ds.flatten)).reverse ++ output) (List.replicate (n + ds.length) true))
      (listTicks e ds) := by
  induction ds generalizing output n with
  | nil => simp [listTicks, records, chunk]; rfl
  | cons d ds ih =>
    have first := entry_exact e d (records (entryEncoding e) ds ++ suffix) output (List.replicate n true)
    have next := ih ((chunk e d).reverse ++ output) (n + 1)
    have all := first.trans (by simpa only [List.replicate_succ] using next)
    simpa [listTicks, records, entryEncoding, chunk, records_append, List.reverse_append,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

/-- Literal byte equality connecting delayed suffix emission to finiteProductCode. -/
theorem output_eq (ds : List (Code A)) :
    (((List.replicate ds.length (chunk e [.swap, .mul]).reverse).flatten ++
      (chunk e [.one]).reverse ++ (chunk e (ds.flatten)).reverse).reverse ++ [false]) =
      (codeEncoding e).encode (product ds) := by
  have rep (n : ℕ) : records (opEncoding e) ((List.replicate n ([.swap, .mul] : Code A)).flatten) =
      (List.replicate n (records (opEncoding e) [.swap, .mul])).flatten := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [List.replicate_succ, List.flatten_cons, records_append] using
        congrArg (fun w => records (opEncoding e) [.swap, .mul] ++ w) ih
  rw [product_stream, code_records]
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_flatten,
    List.map_replicate, List.reverse_replicate, chunk, records_append, rep, List.append_assoc]

/-- Actual clean execution of the entire prepared component list, with exact time.
All framing, count allocation/removal, compiler calls and output cleanup are charged. -/
theorem run_exact (ds : List (Code A)) :
    RunsExactly (driver e).computer.step
      (initList (driver e).computer ((inputEncoding e).encode ds))
      (haltList (driver e).computer ((codeEncoding e).encode (product ds)))
      (listTicks e ds + ds.length + ((codeEncoding e).encode (product ds)).length + 6) := by
  have first := list_exact e ds [false] [] 0
  have last := Components.finish_exact (identityMachine)
    (chunk e [.zero]).reverse (chunk e [.one]).reverse
    (chunk e [.swap, .add]).reverse (chunk e [.swap, .mul]).reverse ds.length
    (chunk e (ds.flatten)).reverse
  simp only [Nat.zero_add, List.replicate_zero, List.append_nil] at first
  have all := first.trans last
  have hin : active (identityMachine) 0
      (records (entryEncoding e) ds ++ [false]) [] [] [] =
      initList (driver e).computer ((inputEncoding e).encode ds) := by
    rw [BinaryCompose.Machine.init_eq]
    unfold Components.active cfg
    congr 1
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [inputEncoding, framedListEncoding, framedList_records, Components.base, Components.tapes, wordTape]
  rw [hin, output_eq e ds] at all
  convert all using 1
  have hl := congrArg List.length (output_eq e ds)
  simp only [List.length_append, List.length_reverse, List.length_singleton] at hl
  simp only [List.length_append, List.length_reverse] at *
  omega

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.CodeProduct
