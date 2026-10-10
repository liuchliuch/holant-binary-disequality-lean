import Holant.Complexity.FixedFieldMachines.Vector
import Holant.Complexity.FixedFieldMachines.Reverse

/-! Executable views of the wiring constructors, independent of proof witnesses
and time polynomials. These equations let VM tests inspect the exact generated
transition systems rather than merely the denoted mathematical functions. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose

abbrev secondMachine : Machine := Wiring.swapMachine.compose Wiring.firstMachine

abbrev rightMapMachine (m : Machine) : Machine :=
  (Wiring.swapMachine.compose (LeftMap.machine m)).compose Wiring.swapMachine

abbrev pairMachine (a b : Machine) : Machine :=
  (Wiring.diagonalMachine.compose (LeftMap.machine a)).compose (rightMapMachine b)

@[simp] theorem rightMapComputes_machine {α β γ : Type} (ea : Encoding α Bool)
    {eb : Encoding β Bool} {ec : Encoding γ Bool} {f : β → γ} (w : Computes eb ec f) :
    (rightMapComputes ea w).machine = rightMapMachine w.machine := rfl

@[simp] theorem pairComputes_machine {α β γ : Type} {ea : Encoding α Bool}
    {eb : Encoding β Bool} {ec : Encoding γ Bool} {f : α → β} {g : α → γ}
    (u : Computes ea eb f) (v : Computes ea ec g) :
    (pairComputes u v).machine = pairMachine u.machine v.machine := rfl

/-- Dimension and index are fixed while compiling, not stored in run-time control. -/
def coordinateMachine : (n : ℕ) → Fin n → Machine
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases Wiring.firstMachine
      (fun j => secondMachine.compose (coordinateMachine n j)) i

@[simp] theorem coordinateComputes_machine (n : ℕ) (i : Fin n) :
    (coordinateComputes n i).machine = coordinateMachine n i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases with
    | zero => rfl
    | succ j =>
      change secondMachine.compose (coordinateComputes n j).machine =
        secondMachine.compose (coordinateMachine n j)
      rw [ih]

end Holant.Complexity.FixedFieldMachines
