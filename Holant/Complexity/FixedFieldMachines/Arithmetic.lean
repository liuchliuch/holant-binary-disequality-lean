import Holant.Complexity.FixedFieldMachines.Vector

/-! Compilation of fixed-dimensional field arithmetic from genuine rational
machine witnesses. This is deliberately a conditional theorem until concrete
canonical rational addition and multiplication providers are connected. Its
premises contain actual finite Boolean-stack programs and timed correctness,
not scalar or vector operations charged as a single machine instruction. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose Holant.Algebraic
open scoped BigOperators

/-- The only outstanding arithmetic provider boundary. Both outputs must use the
literal canonical rational encoding, including cancellation and normalization. -/
structure RationalProvider where
  add : Computes (pairEncoding rationalEncoding rationalEncoding) rationalEncoding
    (fun p => p.1 + p.2)
  mul : Computes (pairEncoding rationalEncoding rationalEncoding) rationalEncoding
    (fun p => p.1 * p.2)

namespace RationalProvider
variable (R : RationalProvider)

noncomputable def addComputes {α : Type} {ea : Encoding α Bool} {f g : α → ℚ}
    (u : Computes ea rationalEncoding f) (v : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun a => f a + g a) :=
  congrComputes ((pairComputes u v).andThen R.add) (fun _ => rfl)

noncomputable def mulComputes {α : Type} {ea : Encoding α Bool} {f g : α → ℚ}
    (u : Computes ea rationalEncoding f) (v : Computes ea rationalEncoding g) :
    Computes ea rationalEncoding (fun a => f a * g a) :=
  congrComputes ((pairComputes u v).andThen R.mul) (fun _ => rfl)

/-- A fixed finite sum compiles recursively into true scalar calls, physical
fanout and intermediate serialization. No accumulator value enters control. -/
noncomputable def sumComputes (R : RationalProvider) {α : Type} (ea : Encoding α Bool) :
    (n : ℕ) → (f : α → Fin n → ℚ) →
    ((i : Fin n) → Computes ea rationalEncoding (fun a => f a i)) →
    Computes ea rationalEncoding (fun a => ∑ i, f a i)
  | 0, f, _ => congrComputes (constantComputes ea rationalEncoding 0) (fun _ => by simp)
  | n + 1, f, w => congrComputes
      (R.addComputes (w 0) (sumComputes R ea n (fun a => Fin.tail (f a)) (fun i => w i.succ)))
      (fun a => by simp [Fin.sum_univ_succ, Fin.tail])

end RationalProvider

/-- Input is an explicit pair of the unchanged canonical coefficient-vector
codes. The extra outer frame is physically parsed by the wiring machines. -/
abbrev vectorPairEncoding (n : ℕ) := pairEncoding (vectorEncoding n) (vectorEncoding n)

noncomputable def leftCoordinateComputes (n : ℕ) (i : Fin n) :
    Computes (vectorPairEncoding n) rationalEncoding (fun p => p.1 i) :=
  congrComputes ((Wiring.firstComputes (vectorEncoding n) (vectorEncoding n)).andThen
    (coordinateComputes n i)) (fun _ => rfl)

noncomputable def rightCoordinateComputes (n : ℕ) (i : Fin n) :
    Computes (vectorPairEncoding n) rationalEncoding (fun p => p.2 i) :=
  congrComputes ((Wiring.secondComputes (vectorEncoding n) (vectorEncoding n)).andThen
    (coordinateComputes n i)) (fun _ => rfl)

/-- Full finite Boolean-stack addition of fixed-dimensional coefficient vectors. -/
noncomputable def additionComputes (R : RationalProvider) (n : ℕ) :
    Computes (vectorPairEncoding n) (vectorEncoding n) (fun p => p.1 + p.2) :=
  assembleComputes (vectorPairEncoding n) n (fun p => p.1 + p.2)
    (fun i => R.addComputes (leftCoordinateComputes n i) (rightCoordinateComputes n i))

/-- A single structure-constant product. The table entry is fixed program syntax
and is loaded by the counted constant machine. -/
noncomputable def tableTermComputes (R : RationalProvider) {n : ℕ} (D : ArithmeticData n)
    (i j k : Fin n) : Computes (vectorPairEncoding n) rationalEncoding
      (fun p => (p.1 i * p.2 j) * D.mulTable i j k) :=
  R.mulComputes
    (R.mulComputes (leftCoordinateComputes n i) (rightCoordinateComputes n j))
    (constantComputes (vectorPairEncoding n) rationalEncoding (D.mulTable i j k))

/-- Full fixed-table multiplication: all coefficient products, summands,
framing, copying, constant pushes and cleanup are actual finite programs. -/
noncomputable def multiplicationComputes (R : RationalProvider) {n : ℕ} (D : ArithmeticData n) :
    Computes (vectorPairEncoding n) (vectorEncoding n) (fun p => D.mulCode p.1 p.2) := by
  apply assembleComputes
  intro k
  have w := R.sumComputes (vectorPairEncoding n) n
    (fun p i => ∑ j, (p.1 i * p.2 j) * D.mulTable i j k)
    (fun i => R.sumComputes (vectorPairEncoding n) n
      (fun p j => (p.1 i * p.2 j) * D.mulTable i j k)
      (fun j => tableTermComputes R D i j k))
  exact congrComputes w (fun p => by simp [ArithmeticData.mulCode, Finset.sum_apply])

/-- Unit coordinates are executable finite constants even without arithmetic
providers; all coefficients retain their original canonical rational encodings. -/
noncomputable def unitComputes {α : Type} (ea : Encoding α Bool) {n : ℕ} (D : ArithmeticData n) :
    Computes ea (vectorEncoding n) (fun _ => D.unitCode) :=
  vectorConstantComputes ea n D.unitCode

/-- The assembled arithmetic package carries real finite programs at both fields. -/
structure Provider {n : ℕ} (D : ArithmeticData n) where
  add : Computes (vectorPairEncoding n) (vectorEncoding n) (fun p => p.1 + p.2)
  mul : Computes (vectorPairEncoding n) (vectorEncoding n) (fun p => D.mulCode p.1 p.2)

noncomputable def provider (R : RationalProvider) {n : ℕ} (D : ArithmeticData n) : Provider D :=
  ⟨additionComputes R n, multiplicationComputes R D⟩

theorem addition_inFP (R : RationalProvider) (n : ℕ) :
    InFP (vectorPairEncoding n) (vectorEncoding n) (fun p => p.1 + p.2) :=
  (additionComputes R n).inFP

theorem multiplication_inFP (R : RationalProvider) {n : ℕ} (D : ArithmeticData n) :
    InFP (vectorPairEncoding n) (vectorEncoding n) (fun p => D.mulCode p.1 p.2) :=
  (multiplicationComputes R D).inFP

end Holant.Complexity.FixedFieldMachines
