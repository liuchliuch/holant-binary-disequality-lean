import Holant.OneHot.StackProgram.Machine.Output
import Holant.Complexity.FixedFieldMachines.Concrete

/-! Instantiation with the genuine canonical rational and fixed-field machines.
The finite field basis and coefficient table are fixed construction data. -/
namespace Holant.OneHot.StackProgram.Machine
open Holant.Algebraic Holant.Complexity Computability

/-- Runtime construction uses only the explicit rational multiplication table. -/
noncomputable def coordinateProviders {n : ℕ} (D : ArithmeticData n) (h : D.Laws) :
    letI := Coordinates.commSemiring h
    Operator.Providers (Coordinates.encoding D) := by
  letI := Coordinates.commSemiring h
  exact {
    add := FixedFieldMachines.Concrete.coordinateAddition D
    mul := FixedFieldMachines.Concrete.coordinateMultiplication D }

/-- The same concrete programs respect the original semantic field codec. -/
noncomputable def fieldProviders {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (F : FixedField K n) : Operator.Providers F.encoding where
  add := FixedFieldMachines.Concrete.fieldAddition F
  mul := FixedFieldMachines.Concrete.fieldMultiplication F

/-- Only the given fixed literal words enter finite instruction syntax. -/
noncomputable def coordinateInterpreter {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}
    (D : ArithmeticData n) (h : D.Laws) (labels : Encoding A Bool) (C : ℕ)
    (coeff : A → Coordinates D)
    (lits : letI := Coordinates.commSemiring h
      Kernels.Literals (Coordinates.encoding D) coeff) : BinaryCompose.Machine := by
  letI := Coordinates.commSemiring h
  exact Interpreter.valueMachine labels C (Coordinates.encoding D) coeff lits (coordinateProviders D h)

noncomputable def fieldInterpreter {A K : Type} [Fintype A] [DecidableEq A]
    [Field K] [Algebra ℚ K] {n : ℕ} (F : FixedField K n)
    (labels : Encoding A Bool) (C : ℕ) (coeff : A → K) (lits : Kernels.Literals F.encoding coeff) :=
  Interpreter.valueMachine labels C F.encoding coeff lits (fieldProviders F)

end Holant.OneHot.StackProgram.Machine
