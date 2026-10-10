import Holant.Complexity.FixedFieldMachines.CoordinateBridge
import Holant.Complexity.FixedFieldMachines.PrimitiveCost
import Holant.Complexity.RationalArithmetic.Operations

/-! Unconditional fixed-field arithmetic, integrating the fully verified literal
canonical rational addition and multiplication programs. No machine-correctness
hypothesis or unit-cost arithmetic operation remains at this boundary. -/
namespace Holant.Complexity.FixedFieldMachines.Concrete
open Computability BinaryCompose Holant.Algebraic

noncomputable def rationalProvider : RationalProvider where
  add := RationalArithmetic.additionComputes
  mul := RationalArithmetic.multiplicationComputes

/-- Actual finite Boolean-stack addition on the original coefficient-vector codec. -/
noncomputable def addition (n : ℕ) := additionComputes rationalProvider n

/-- Actual fixed-table multiplication on the original coefficient-vector codec. -/
noncomputable def multiplication {n : ℕ} (D : ArithmeticData n) :=
  multiplicationComputes rationalProvider D

/-- Ready-to-use arithmetic provider for finite stack interpreters. -/
noncomputable def provider {n : ℕ} (D : ArithmeticData n) : Provider D :=
  FixedFieldMachines.provider rationalProvider D

theorem addition_inFP (n : ℕ) :
    InFP (vectorPairEncoding n) (vectorEncoding n) (fun p => p.1 + p.2) :=
  (addition n).inFP

theorem multiplication_inFP {n : ℕ} (D : ArithmeticData n) :
    InFP (vectorPairEncoding n) (vectorEncoding n) (fun p => D.mulCode p.1 p.2) :=
  (multiplication D).inFP

noncomputable def coordinateAddition {n : ℕ} (D : ArithmeticData n) :=
  coordinateAdditionComputes rationalProvider D
noncomputable def coordinateMultiplication {n : ℕ} (D : ArithmeticData n) :=
  coordinateMultiplicationComputes rationalProvider D

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

/-- End-to-end semantic field addition using the pre-existing field encoding. -/
noncomputable def fieldAddition (F : FixedField K n) :=
  existingFieldAdditionComputes rationalProvider F

/-- End-to-end semantic field multiplication using only fixed table data at runtime. -/
noncomputable def fieldMultiplication (F : FixedField K n) :=
  existingFieldMultiplicationComputes rationalProvider F

theorem fieldAddition_inFP (F : FixedField K n) :
    InFP (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 + p.2) :=
  (fieldAddition F).inFP

theorem fieldMultiplication_inFP (F : FixedField K n) :
    InFP (pairEncoding F.encoding F.encoding) F.encoding (fun p => p.1 * p.2) :=
  (fieldMultiplication F).inFP

end Holant.Complexity.FixedFieldMachines.Concrete
