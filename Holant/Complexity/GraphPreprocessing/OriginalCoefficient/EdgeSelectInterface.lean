import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelectEncoding
import Holant.Complexity.GraphPreprocessing.Primitive

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
open Turing Computability StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false

def ticks (x : Input) : ℕ := 3*(ReachRound.encode x.1).length+3*x.2.1.val+10

theorem exact_run (x : Input) :
    RunsExactly machine.computer.step (initList machine.computer (inputEncoding.encode x))
      (haltList machine.computer (UnaryBinary.unaryEncoding.encode (value x))) (ticks x) := by
  let e := x.1.get x.2.1
  have split : x.1.take x.2.1.val++e::x.1.drop (x.2.1.val+1)=x.1 := by
    have h := List.take_append_drop x.2.1.val x.1
    rw [List.drop_eq_getElem_cons x.2.1.isLt] at h
    exact h
  have hl : (x.1.take x.2.1.val).length=x.2.1.val := List.length_take_of_le (Nat.le_of_lt x.2.1.isLt)
  have h := exact_split (x.1.take x.2.1.val) (x.1.drop (x.2.1.val+1)) e.1 e.2 x.2.2
  rw [split,hl] at h
  exact h

theorem ticks_le (x : Input) : ticks x≤2*(inputEncoding.encode x).length+4 := by
  simp only [ticks,input_word,List.length_append,Holant.Algebraic.frame_length,List.length_replicate,List.length_singleton]
  omega

noncomputable def computes : Computes inputEncoding UnaryBinary.unaryEncoding value where
  machine := machine
  time := 2*Polynomial.X+4
  outputs x := {steps := ticks x,evals_in_steps := exact_run x,steps_le_m := by simpa using ticks_le x}
theorem inFP : InFP inputEncoding UnaryBinary.unaryEncoding value := computes.inFP

theorem program_budget (label : Fin 16) : TM2Cost.budget (program label)≤8 := by
  fin_cases label <;> simp [program,Frame.scanStmt_budget,UnarySkip.statement,UnaryField.statement,
    clearStmt,copyMoveStmt,TM2Cost.budget]
theorem primitive_bound (x : Input) :
    (Primitive.run program (ticks x) (some (initList machine.computer (inputEncoding.encode x)))).2 =
      some (haltList machine.computer (UnaryBinary.unaryEncoding.encode (value x))) ∧
    (Primitive.run program (ticks x) (some (initList machine.computer (inputEncoding.encode x)))).1 ≤
      8*(2*(inputEncoding.encode x).length+4) := by
  have h := Primitive.execution_cost program 8 program_budget _ _ _ (exact_run x)
  exact ⟨h.1,le_trans h.2 (Nat.mul_le_mul_left _ (ticks_le x))⟩

theorem error_step (memory : Option Bool × Unit) (stack : Fin 5 → List Bool) :
    machine.computer.step (⟨some 15,memory,stack⟩ : machine.Config)=
      some (⟨none,(some false,()),stack⟩ : machine.Config) := rfl
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeSelect
