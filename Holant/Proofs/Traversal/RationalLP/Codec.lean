import Holant.Complexity.IntegerArithmetic.Encoding
import Holant.Complexity.RationalArithmetic.Operations
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.GraphPreprocessing.OccurrenceLabel


namespace Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec
open Holant.Complexity Computability BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section

@[ext] structure Raw where
  rowCount : ℕ
  dimension : ℕ
  rows : List (List ℤ)
  rhs : List ℤ
  deriving DecidableEq

abbrev Wire := ℕ × (ℕ × (List (List ℤ) × List ℤ))
def rowEncoding := framedListEncoding IntegerArithmetic.encoding
def rowsEncoding := framedListEncoding rowEncoding
def wireEncoding := pairEncoding UnaryBinary.unaryEncoding
  (pairEncoding UnaryBinary.unaryEncoding (pairEncoding rowsEncoding rowEncoding))
def Raw.wire (d : Raw) : Wire := (d.rowCount,d.dimension,d.rows,d.rhs)
def fromWire (p : Wire) : Raw := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩

def encoding : Encoding Raw Bool where
  encode d := wireEncoding.encode d.wire
  decode bits := (wireEncoding.decode bits).map fromWire
  decode_encode d := by simp; rfl

def Raw.WellFormed (d : Raw) : Prop :=
  d.rows.length = d.rowCount ∧ d.rhs.length = d.rowCount ∧
    ∀ row ∈ d.rows, row.length = d.dimension
instance (d : Raw) : Decidable d.WellFormed := by unfold Raw.WellFormed; infer_instance
abbrev Input := {d : Raw // d.WellFormed}
def inputEncoding : Encoding Input Bool where
  encode d := encoding.encode d.val
  decode bits := do
    let d ← encoding.decode bits
    if h : d.WellFormed then some ⟨d,h⟩ else none
  decode_encode d := by simp [d.property]

def Raw.coefficient (d : Raw) (i : Fin d.rowCount) (j : Fin d.dimension) : ℤ :=
  (d.rows.getD i.val []).getD j.val 0
def Raw.constant (d : Raw) (i : Fin d.rowCount) : ℤ := d.rhs.getD i.val 0

def Feasible (d : Raw) (x : Fin d.dimension → ℚ) : Prop :=
  (∀ i, ∑ j, (d.coefficient i j : ℚ)*x j = d.constant i) ∧
    ∀ j, 0 ≤ x j ∧ x j ≤ 1
def Positive (d : Raw) (j : Fin d.dimension) : Prop := ∃ x, Feasible d x ∧ 0 < x j

def pointEncoding := framedListEncoding Holant.Algebraic.rationalEncoding
def outputEncoding := optionEncoding pointEncoding
def point (d : Raw) (xs : List ℚ) : Fin d.dimension → ℚ := fun j => xs.getD j.val 0
def Solution (d : Raw) (xs : List ℚ) : Prop := xs.length = d.dimension ∧ Feasible d (point d xs)
def Response (d : Raw) : Option (List ℚ) → Prop
  | none => ¬ ∃ x, Feasible d x
  | some xs => Solution d xs

abbrev CoordinateQuery := Σ d : Input, Fin d.val.dimension
def coordinateEncoding := sigmaEncoding inputEncoding
  (fun d => OccurrenceLabel.unaryPortEncoding d.val.dimension)

/-- The EO owner can instantiate this exact generic tuple after emitting its
own dense matrix. This constructor is semantic; it is not a matrix compiler. -/
def pack (m n : ℕ) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : Input :=
  ⟨⟨m,n,List.ofFn (fun i => List.ofFn (A i)),List.ofFn b⟩,by simp [Raw.WellFormed]⟩

@[simp] theorem pack_coefficient (m n : ℕ) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (i : Fin m) (j : Fin n) : (pack m n A b).val.coefficient i j = A i j := by
  simp [pack,Raw.coefficient,List.getD_eq_getElem]
@[simp] theorem pack_constant (m n : ℕ) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (i : Fin m) : (pack m n A b).val.constant i = b i := by
  simp [pack,Raw.constant,List.getD_eq_getElem]

theorem pack_feasible (m n : ℕ) (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℚ) : Feasible (pack m n A b).val x ↔
      (∀ i, ∑ j, (A i j : ℚ)*x j = b i) ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  change ((∀ i : Fin m, ∑ j : Fin n, ((pack m n A b).val.coefficient i j : ℚ)*x j =
    (pack m n A b).val.constant i) ∧ ∀ j : Fin n, 0 ≤ x j ∧ x j ≤ 1) ↔ _
  simp only [pack_coefficient,pack_constant]

end
end Holant.LocalDrafts.TraversalCompletion.RationalLP.Codec
