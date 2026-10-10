import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Complexity.RationalArithmetic.StateChecks

/-! Structural raw projection for a genuinely returning optional provider. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMap.Raw
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Turing.TM2.Stmt
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable (m : RawMachine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

abbrev Keys := m.K ⊕ Bool
abbrev Labels := m.Label ⊕ Fin 11

def program : Labels m → Stmt (Keys m) (Labels m) m.State
  | .inl l => embedStmt (RawMachine.frameLayout m) (RawMachine.frameStates m) Sum.inl (some (.inr (3 : Fin 11))) (m.program l)
  | .inr l => match l.val with
    | 0 => pop (.inr false) (fun v bit => (bit,v.2))
      (branch (fun v => v.1 == some true)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 1)))
        (branch (fun v => v.1 == some false)
          (load (fun v => (none,v.2)) (goto (fun _ => .inr 6)))
          (load (fun v => (none,v.2)) (goto (fun _ => .inr 8)))))
    | 1 => copyMoveStmt (.inr false) (.inr true) (.inr 1) (.inr 2)
    | 2 => copyMoveStmt (.inr true) (.inl m.input) (.inr 2) (.inl m.main)
    | 3 => copyMoveStmt (.inl m.output) (.inr true) (.inr 3) (.inr 4)
    | 4 => copyMoveStmt (.inr true) (.inr false) (.inr 4) (.inr 5)
    | 5 => push (.inr false) (fun _ => true) .halt
    | 6 => pop (.inr false) (fun v bit => (bit,v.2))
      (branch (fun v => v.1.isSome)
        (load (fun v => (none,v.2)) (goto (fun _ => .inr 8)))
        (push (.inr false) (fun _ => false) (load (fun v => (none,v.2)) .halt)))
    | 8 => clearStmt (.inr false) (.inr 8) (.inr 9)
    | 9 => clearStmt (.inr true) (.inr 9) (.inr 10)
    | _ => .halt

def machine : RawMachine where
  K := Keys m
  input := .inr false
  output := .inr false
  Label := Labels m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMap.Raw

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMap
open Turing Computability BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false
theorem erase_machine (m : Machine) : RawMachine.erase (machine m)=Raw.machine (RawMachine.erase m) := by
  unfold RawMachine.erase machine Raw.machine
  congr 1
  funext label
  cases label with
  | inl l => rfl
  | inr l => rfl
def rawCheck {r : RawMachine} (h : RationalArithmetic.StateCheck r) : RationalArithmetic.StateCheck (Raw.machine r) where
  inspect state := state.1.isNone && h.inspect state.2
  correct state := by
    rcases state with ⟨flag,state⟩
    cases flag <;> simp [Raw.machine,Bool.and_eq_true,h.correct]
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMap
