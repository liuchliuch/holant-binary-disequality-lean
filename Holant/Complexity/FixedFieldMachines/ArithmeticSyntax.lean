import Holant.Complexity.FixedFieldMachines.Arithmetic
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! Computable syntax constructors for fixed-field machines. These depend only
on the two concrete scalar programs, the dimension and rational table constants.
The equalities identify them with the proved conditional witnesses, so execution
tests need not evaluate noncomputable time-polynomial proof packages. -/
namespace Holant.Complexity.FixedFieldMachines.Syntax
open BinaryCompose Holant.Algebraic

structure Scalars where
  add : Machine
  mul : Machine

def ofProvider (R : RationalProvider) : Scalars := ⟨R.add.machine, R.mul.machine⟩

abbrev scalarAdd (R : Scalars) (a b : Machine) : Machine := (pairMachine a b).compose R.add
abbrev scalarMul (R : Scalars) (a b : Machine) : Machine := (pairMachine a b).compose R.mul

def sum (R : Scalars) : (n : ℕ) → (Fin n → Machine) → Machine
  | 0, _ => Constant.machine (rationalEncoding.encode 0)
  | n + 1, w => scalarAdd R (w 0) (sum R n (fun i => w i.succ))

def assemble : (n : ℕ) → (Fin n → Machine) → Machine
  | 0, _ => Constant.machine []
  | n + 1, w => pairMachine (w 0) (assemble n (fun i => w i.succ))

abbrev leftCoordinate (n : ℕ) (i : Fin n) : Machine := Wiring.firstMachine.compose (coordinateMachine n i)
abbrev rightCoordinate (n : ℕ) (i : Fin n) : Machine := secondMachine.compose (coordinateMachine n i)

def addition (R : Scalars) (n : ℕ) : Machine :=
  assemble n (fun i => scalarAdd R (leftCoordinate n i) (rightCoordinate n i))

def multiplication (R : Scalars) {n : ℕ} (D : ArithmeticData n) : Machine :=
  assemble n (fun k => sum R n (fun i => sum R n (fun j =>
    scalarMul R (scalarMul R (leftCoordinate n i) (rightCoordinate n j))
      (Constant.machine (rationalEncoding.encode (D.mulTable i j k))))))

open Computability

@[simp] theorem sum_machine (R : RationalProvider) {α : Type} (ea : Encoding α Bool)
    (n : ℕ) (f : α → Fin n → ℚ)
    (w : (i : Fin n) → Computes ea rationalEncoding (fun a => f a i)) :
    (R.sumComputes ea n f w).machine = sum (ofProvider R) n (fun i => (w i).machine) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change scalarAdd (ofProvider R) (w 0).machine
      (R.sumComputes ea n (fun a => Fin.tail (f a)) (fun i => w i.succ)).machine = _
    exact congrArg (scalarAdd (ofProvider R) (w 0).machine)
      (ih (fun a => Fin.tail (f a)) (fun i => w i.succ))

@[simp] theorem assemble_machine {α : Type} (ea : Encoding α Bool)
    (n : ℕ) (f : α → Fin n → ℚ)
    (w : (i : Fin n) → Computes ea rationalEncoding (fun a => f a i)) :
    (assembleComputes ea n f w).machine = assemble n (fun i => (w i).machine) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pairMachine (w 0).machine
      (assembleComputes ea n (fun a => Fin.tail (f a)) (fun i => w i.succ)).machine = _
    exact congrArg (pairMachine (w 0).machine)
      (ih (fun a => Fin.tail (f a)) (fun i => w i.succ))

@[simp] theorem leftCoordinate_machine (n : ℕ) (i : Fin n) :
    (leftCoordinateComputes n i).machine = leftCoordinate n i := by
  change Wiring.firstMachine.compose (coordinateComputes n i).machine = _
  rw [coordinateComputes_machine]

@[simp] theorem rightCoordinate_machine (n : ℕ) (i : Fin n) :
    (rightCoordinateComputes n i).machine = rightCoordinate n i := by
  change secondMachine.compose (coordinateComputes n i).machine = _
  rw [coordinateComputes_machine]

@[simp] theorem addition_machine (R : RationalProvider) (n : ℕ) :
    (additionComputes R n).machine = addition (ofProvider R) n := by
  unfold additionComputes addition
  rw [assemble_machine]
  congr 1
  funext i
  change scalarAdd (ofProvider R) (leftCoordinateComputes n i).machine
    (rightCoordinateComputes n i).machine = _
  rw [leftCoordinate_machine, rightCoordinate_machine]

@[simp] theorem multiplication_machine (R : RationalProvider) {n : ℕ} (D : ArithmeticData n) :
    (multiplicationComputes R D).machine = multiplication (ofProvider R) D := by
  unfold multiplicationComputes multiplication
  rw [assemble_machine]
  congr 1
  funext k
  change (R.sumComputes _ _ _ _).machine = _
  rw [sum_machine]
  congr 1
  funext i
  rw [sum_machine]
  congr 1
  funext j
  change scalarMul (ofProvider R)
    (scalarMul (ofProvider R) (leftCoordinateComputes n i).machine (rightCoordinateComputes n j).machine)
    (Constant.machine (rationalEncoding.encode (D.mulTable i j k))) = _
  rw [leftCoordinate_machine, rightCoordinate_machine]

end Holant.Complexity.FixedFieldMachines.Syntax
