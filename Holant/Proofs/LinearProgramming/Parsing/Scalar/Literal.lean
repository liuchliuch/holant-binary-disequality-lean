import Holant.Proofs.LinearProgramming.Parsing.FramePrefix

open Holant.Complexity

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Scalar
open Holant Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.OneHot.StackProgram.GraphLabelEncoding (optionEncoding)
noncomputable section
namespace Literal
/-- Serialization here is literally identity on the already encoded input.
It does not compute or inspect a value in the finite statement program. -/
def bytes {A : Type} (ea : Encoding A Bool) : Computes ea Frame.wordEncoding ea.encode :=
  recode (identityComputes ea) id (fun _ => rfl) (fun _ => rfl)

abbrev someMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Option Bool × Unit
  initial := (none,())
  program _ := .push () (fun _ => true) .halt

theorem some_exact (word : List Bool) : RunsExactly someMachine.computer.step
    (initList someMachine.computer word) (haltList someMachine.computer (true::word)) 1 := by
  change someMachine.computer.step (initList someMachine.computer word)=
    some (haltList someMachine.computer (true::word))
  rw [Machine.init_eq,Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (wordTape () word) () (true::word)⟩ : someMachine.Config)=_
  congr 2

def someComputes {A : Type} (ea : Encoding A Bool) :
    Computes ea (optionEncoding ea) Option.some where
  machine := someMachine
  time := 1
  outputs a := {
    steps := 1
    evals_in_steps := some_exact (ea.encode a)
    steps_le_m := by simp }
end Literal
end
end Holant.LocalDrafts.RemoteWork.RationalLP.Parsing.Scalar
