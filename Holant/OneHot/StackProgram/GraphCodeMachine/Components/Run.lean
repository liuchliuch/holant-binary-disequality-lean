import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Compile

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable {A : Type} [Fintype A] (e : Encoding A Bool) (C : ℕ)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def listTicks (ds : List (Descriptor A)) : ℕ := (ds.map (descriptorTicks e)).sum

variable (hlabels : ∀ x, (e.encode x).length ≤ C)
include hlabels

/-- Complete streaming loop with an arbitrary retained suffix and accumulated bits. -/
theorem list_exact (ds : List (Descriptor A)) (suffix output : List Bool) (n : ℕ) :
    RunsExactly (driver e C).computer.step
      (active (GraphCodeMachine.machine e C .closed) 0
        (records (encoding e) ds ++ suffix) [] output (List.replicate n true))
      (active (GraphCodeMachine.machine e C .closed) 0 suffix []
        ((chunk e (ds.flatMap componentCode)).reverse ++ output) (List.replicate (n + ds.length) true))
      (listTicks e ds) := by
  induction ds generalizing output n with
  | nil => simp [listTicks, records, chunk]; rfl
  | cons d ds ih =>
    have first := descriptor_exact e C hlabels d (records (encoding e) ds ++ suffix) output (List.replicate n true)
    have next := ih ((chunk e (componentCode d)).reverse ++ output) (n + 1)
    have all := first.trans (by simpa only [List.replicate_succ] using next)
    simpa [listTicks, records, encoding, chunk, records_append, List.reverse_append,
      List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

omit hlabels [Fintype A] in
/-- Literal byte equality connecting delayed suffix emission to finiteProductCode. -/
theorem output_eq (ds : List (Descriptor A)) :
    (((List.replicate ds.length (chunk e [.swap, .mul]).reverse).flatten ++
      (chunk e [.one]).reverse ++ (chunk e (ds.flatMap componentCode)).reverse).reverse ++ [false]) =
      (codeEncoding e).encode (productCode ds) := by
  have rep (n : ℕ) : records (opEncoding e) ((List.replicate n ([.swap, .mul] : Code A)).flatten) =
      (List.replicate n (records (opEncoding e) [.swap, .mul])).flatten := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simpa only [List.replicate_succ, List.flatten_cons, records_append] using
        congrArg (fun w => records (opEncoding e) [.swap, .mul] ++ w) ih
  rw [productCode_stream, code_records]
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_flatten,
    List.map_replicate, List.reverse_replicate, chunk, records_append, rep, List.append_assoc]

/-- Actual clean execution of the entire prepared component list, with exact time.
All framing, count allocation/removal, compiler calls and output cleanup are charged. -/
theorem run_exact (ds : List (Descriptor A)) :
    RunsExactly (driver e C).computer.step
      (initList (driver e C).computer ((listEncoding e).encode ds))
      (haltList (driver e C).computer ((codeEncoding e).encode (productCode ds)))
      (listTicks e ds + ds.length + ((codeEncoding e).encode (productCode ds)).length + 6) := by
  have first := list_exact e C hlabels ds [false] [] 0
  have last := finish_exact (GraphCodeMachine.machine e C .closed)
    (chunk e [.zero]).reverse (chunk e [.one]).reverse
    (chunk e [.swap, .add]).reverse (chunk e [.swap, .mul]).reverse ds.length
    (chunk e (ds.flatMap componentCode)).reverse
  simp only [Nat.zero_add, List.replicate_zero, List.append_nil] at first
  have all := first.trans last
  have hin : active (GraphCodeMachine.machine e C .closed) 0
      (records (encoding e) ds ++ [false]) [] [] [] =
      initList (driver e C).computer ((listEncoding e).encode ds) := by
    rw [BinaryCompose.Machine.init_eq]
    unfold active cfg
    congr 1
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> simp [listEncoding, framedListEncoding, framedList_records, base, tapes, wordTape]
  rw [hin, output_eq e ds] at all
  convert all using 1
  have hl := congrArg List.length (output_eq e ds)
  simp only [List.length_append, List.length_reverse, List.length_singleton] at hl
  simp only [List.length_append, List.length_reverse] at *
  omega

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
