import Holant.OneHot.StackProgram.Machine.Output
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Primitive-instruction accounting for the full interpreter. The fixed program
budget includes every encoded literal bit, finite decoder branch and embedded
arithmetic instruction; it is independent of the input bytecode length. -/
namespace Holant.OneHot.StackProgram.Machine.Interpreter
open Turing Computability Holant.Complexity
variable {A V : Type} [Fintype A] [DecidableEq A] [CommSemiring V]
variable (labels : Encoding A Bool) (C : ℕ) (e : Encoding V Bool) (coeff : A → V)
variable (lits : Kernels.Literals e coeff) (providers : Operator.Providers e)

/-- Timed clean output and actual primitive cost share the same real execution. -/
theorem value_with_primitive_cost (hlabels : ∀ a, (labels.encode a).length ≤ C)
    {W H : ℕ} {code : Code A} {value : V} {trace : List V}
    (h : Certified e coeff W H code [] [value] trace) :
    ∃ time, time ≤ code.length * instructionBound C e providers W H + 6 * W + 16 ∧
      Kernels.Executes (valueMachine labels C e coeff lits providers)
        ((codeEncoding labels).encode code) (e.encode value) time ∧
      FixedFieldMachines.primitiveCost (valueMachine labels C e coeff lits providers) time
        (some (initList (valueMachine labels C e coeff lits providers).computer
          ((codeEncoding labels).encode code))) ≤
        (code.length * instructionBound C e providers W H + 6 * W + 16) *
          (valueMachine labels C e coeff lits providers).primitiveBudget := by
  obtain ⟨time, ht, hr⟩ := value_exact labels C e coeff lits providers hlabels h
  exact ⟨time, ht, hr, le_trans (FixedFieldMachines.primitiveCost_le _ _ _)
    (Nat.mul_le_mul_right _ ht)⟩

end Holant.OneHot.StackProgram.Machine.Interpreter
