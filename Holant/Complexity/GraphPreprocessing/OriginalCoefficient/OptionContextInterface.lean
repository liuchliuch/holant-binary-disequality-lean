import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContext
import Holant.Complexity.GraphPreprocessing.Primitive

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContext
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)

def inputEncoding := pairEncoding ea (optionEncoding eb)
def outputEncoding := optionEncoding (pairEncoding ea eb)
def value (x : α × Option β) : Option (α × β) := x.2.map (fun b => (x.1,b))
def ticks (x : α × Option β) : ℕ := match x.2 with
  | none => 3*(ea.encode x.1).length+5
  | some b => 4*(ea.encode x.1).length+2*(eb.encode b).length+9

theorem exact_run (x : α × Option β) :
    RunsExactly machine.computer.step (initList machine.computer ((inputEncoding ea eb).encode x))
      (haltList machine.computer ((outputEncoding ea eb).encode (value x))) (ticks ea eb x) := by
  rcases x with ⟨a,q⟩
  cases q with
  | none => exact none_exact (ea.encode a)
  | some b => exact some_exact (ea.encode a) (eb.encode b)

theorem ticks_le (x : α × Option β) : ticks ea eb x≤2*((inputEncoding ea eb).encode x).length+5 := by
  rcases x with ⟨a,q⟩
  cases q <;> simp [ticks,inputEncoding,pairEncoding,optionEncoding,Holant.Algebraic.frame_length] <;> omega

noncomputable def computes : Computes (inputEncoding ea eb) (outputEncoding ea eb) value where
  machine := machine
  time := 2*Polynomial.X+5
  outputs x := {steps := ticks ea eb x,evals_in_steps := exact_run ea eb x,steps_le_m := by simpa using ticks_le ea eb x}
theorem inFP : InFP (inputEncoding ea eb) (outputEncoding ea eb) value := (computes ea eb).inFP

theorem program_budget (label : Fin 12) : TM2Cost.budget (program label)≤8 := by
  fin_cases label <;> simp [program,Frame.scanStmt_budget,FrameEmit.delimiterStmt,FrameEmit.emitStmt,clearStmt,copyMoveStmt,TM2Cost.budget]

theorem primitive_bound (x : α × Option β) :
    (Primitive.run program (ticks ea eb x) (some (initList machine.computer ((inputEncoding ea eb).encode x)))).2 =
      some (haltList machine.computer ((outputEncoding ea eb).encode (value x))) ∧
    (Primitive.run program (ticks ea eb x) (some (initList machine.computer ((inputEncoding ea eb).encode x)))).1 ≤
      8*(2*((inputEncoding ea eb).encode x).length+5) := by
  have h := Primitive.execution_cost program 8 program_budget _ _ _ (exact_run ea eb x)
  exact ⟨h.1,le_trans h.2 (Nat.mul_le_mul_left _ (ticks_le ea eb x))⟩
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContext
