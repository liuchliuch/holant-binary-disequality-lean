import Holant.OneHot.StackProgram.GraphCodeMachine.Components.Control

namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Turing Computability Holant.Complexity BinaryCompose StackProtocol
variable (m : BinaryCompose.Machine) (z o a p : List Bool)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The only output-list terminator is installed before the final physical reversal. -/
theorem clean_exact (word : List Bool) :
    RunsExactly (machine m z o a p).computer.step
      (active m 22 [] [] word [])
      (haltList (machine m z o a p).computer (word.reverse ++ [false])) (word.length + 4) := by
  have first : (machine m z o a p).computer.step (active m 22 [] [] word []) =
      some (active m 23 [] [] (false :: word) []) := by
    change some (cfg (Sum.inr 23 : Labels m) m.initial
      (Function.update (base m [] [] word []) (.inr 3) (false :: word))) = _
    congr 2; funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have h := copy_move_exact (.inr 3 : Keys m) (.inr 5) (.inr 4)
    (by simp) (by simp) (machine m z o a p).computer.step (.inr 23) (.inr 24)
    (executesAt_tm2 _ _ _ rfl) m.initial (fun _ => []) (false :: word) [] []
  have hs : tapes3 (fun _ : Keys m => []) (.inr 3) (.inr 5) (.inr 4) (false :: word) [] [] =
      base m [] [] (false :: word) [] := by
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have ht : tapes3 (fun _ : Keys m => []) (.inr 3) (.inr 5) (.inr 4)
      [] [] ((false :: word).reverse ++ []) =
      tapes m [] [] [] [] (word.reverse ++ [false]) [] := by
    simp only [List.reverse_cons, List.append_nil]
    funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  rw [hs, ht] at h
  have last : (machine m z o a p).computer.step
      (cfg (.inr 24) m.initial (tapes m [] [] [] [] (word.reverse ++ [false]) [])) =
      some (haltList (machine m z o a p).computer (word.reverse ++ [false])) := by
    rw [BinaryCompose.Machine.halt_eq]
    change some (⟨none, (none, m.initial), tapes m [] [] [] [] (word.reverse ++ [false]) []⟩ : Config m) = _
    congr 2; funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  convert ((runsExactly_one first).trans h).trans (runsExactly_one last) using 1
  simp; omega

/-- All count bits, descriptor/input tapes, worker tapes and registers finish clean. -/
theorem finish_exact (n : ℕ) (output : List Bool) :
    RunsExactly (machine m z o a p).computer.step
      (active m 0 [false] [] output (List.replicate n true))
      (haltList (machine m z o a p).computer
        (((List.replicate n p).flatten ++ o ++ output).reverse ++ [false]))
      (n + ((List.replicate n p).flatten ++ o ++ output).length + 7) := by
  have fetch : (machine m z o a p).computer.step
      (active m 0 [false] [] output (List.replicate n true)) =
      some (active m 18 [] [] output (List.replicate n true)) := by
    change some (cfg (Sum.inr 18 : Labels m) m.initial
      (Function.update (base m [false] [] output (List.replicate n true)) (.inr 0) [])) = _
    congr 2; funext key; cases key with
    | inl k => rfl
    | inr k => fin_cases k <;> rfl
  have load := push_exact m z o a p 18 21 o rfl [] [] output (List.replicate n true)
  have counted := count_exact m z o a p n (o ++ output)
  have clean := clean_exact m z o a p ((List.replicate n p).flatten ++ (o ++ output))
  have all := (((runsExactly_one fetch).trans (runsExactly_one load)).trans counted).trans clean
  simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
