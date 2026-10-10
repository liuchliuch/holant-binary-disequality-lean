import Holant.Complexity.BinaryCompose.OutputBound

/-! Identity witnesses with aliased input/output stacks, and their compiled runs. -/

namespace Holant.Complexity.BinaryCompose
open Turing Computability

abbrev identityMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  program _ := .halt

theorem identity_step (word : List Bool) :
    identityMachine.computer.step (initList identityMachine.computer word) =
      some (haltList identityMachine.computer word) := by
  rfl

noncomputable def identityComputes {α : Type} (e : Encoding α Bool) : Computes e e id where
  machine := identityMachine
  time := 1
  outputs a :=
    { steps := 1
      evals_in_steps := identity_step (e.encode a)
      steps_le_m := by simp }

/-- Exact clean execution with aliasing in both components, for arbitrary words,
including malformed natural encodings and the empty input. -/
theorem identity_compose_exact (word : List Bool) :
    (fun p => p.bind (identityMachine.compose identityMachine).computer.step)^[2 * word.length + 4]
      (some (initList (identityMachine.compose identityMachine).computer word)) =
      some (haltList (identityMachine.compose identityMachine).computer word) := by
  have h := Machine.compose_run identityMachine identityMachine word word word 1 1
    (identity_step word) (identity_step word)
  have hn : 1 + (2 * (word.length + 1) + 1) = 2 * word.length + 4 := by omega
  rw [hn] at h
  exact h

end Holant.Complexity.BinaryCompose
