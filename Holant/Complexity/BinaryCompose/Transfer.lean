import Holant.Complexity.BinaryCompose.Interface
import Holant.Complexity.StackProtocol

/-! A destructive, order-preserving transfer using exactly two stack-reversal
passes. Empty-stack tests and scratch-register resets are included in the count. -/

namespace Holant.Complexity.BinaryCompose
open Turing StackProtocol

variable {K Λ τ : Type} [DecidableEq K]

private theorem tapes3_first (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (word : List Bool) :
    tapes3 (fun _ => []) src dst tmp word [] [] = wordTape src word := by
  funext k
  by_cases h : k = src
  · subst k; simp [tapes3, wordTape, hsd, hst]
  · simp [tapes3, wordTape, Function.update_apply, h]

private theorem tapes3_last (src dst tmp : K) (word : List Bool) :
    tapes3 (fun _ => []) src dst tmp [] [] word = wordTape tmp word := by
  simp [tapes3, wordTape]

/-- The first pass consumes source into temporary; the second consumes temporary
into destination. Every non-destination stack is empty on return. There is no
assumption connecting either stack to a component machine's input/output alias. -/
theorem transfer_exact (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (word : List Bool) :
    RunsExactly step (cfg move memory (wordTape src word))
      (cfg next memory (wordTape dst word)) (2 * (word.length + 1)) := by
  have first := copy_move_exact src dst tmp hsd hst step move restore hm
    memory (fun _ => []) word [] []
  simp only [List.append_nil, tapes3_first src dst tmp hsd hst,
    tapes3_last] at first
  have second := copy_move_exact tmp src dst (Ne.symm hst) (Ne.symm hdt)
    step restore next hr memory (fun _ => []) word.reverse [] []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse,
    tapes3_first tmp src dst (Ne.symm hst) (Ne.symm hdt), tapes3_last] at second
  simpa [Nat.two_mul] using first.trans second

/-- The transfer overhead is a genuine timed ordinary-machine execution. -/
def transfer_correct (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (move restore next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (word : List Bool) :
    StateTransition.EvalsToInTime step (cfg move memory (wordTape src word))
      (some (cfg next memory (wordTape dst word))) (2 * (word.length + 1)) :=
  (transfer_exact step src dst tmp hsd hst hdt move restore next hm hr memory word).toTimed

end Holant.Complexity.BinaryCompose
