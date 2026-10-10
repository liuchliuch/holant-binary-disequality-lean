import Holant.Complexity.FixedFieldMachines.LeftMap
import Holant.Complexity.FixedFieldMachines.Constant
import Holant.Algebraic.FixedField

/-! Fixed-length rational vectors are handled using their existing ordered
framed scalar codec. The dimension is compiled into finite programs; it is not
an unbounded run-time register. These operations require no rational arithmetic. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose Holant.Algebraic

noncomputable def headComputes (n : ℕ) :
    Computes (vectorEncoding (n + 1)) rationalEncoding (fun v => v 0) :=
  recode (Wiring.firstComputes rationalEncoding (vectorEncoding n))
    (fun v => (v 0, Fin.tail v)) (fun _ => rfl) (fun _ => rfl)

noncomputable def tailComputes (n : ℕ) :
    Computes (vectorEncoding (n + 1)) (vectorEncoding n) Fin.tail :=
  recode (Wiring.secondComputes rationalEncoding (vectorEncoding n))
    (fun v => (v 0, Fin.tail v)) (fun _ => rfl) (fun _ => rfl)

/-- The finite index chooses a finite chain of real parsing/erasing machines. -/
noncomputable def coordinateComputes : (n : ℕ) → (i : Fin n) →
    Computes (vectorEncoding n) rationalEncoding (fun v => v i)
  | 0, i => Fin.elim0 i
  | n + 1, i => Fin.cases (headComputes n)
      (fun j => congrComputes ((tailComputes n).andThen (coordinateComputes n j)) (fun _ => rfl)) i

/-- Assemble independently computed scalar coordinates. Each inductive step
physically duplicates the input, runs both programs and serializes the head. -/
noncomputable def assembleComputes {α : Type} (ea : Encoding α Bool) :
    (n : ℕ) → (f : α → Fin n → ℚ) →
    ((i : Fin n) → Computes ea rationalEncoding (fun a => f a i)) →
    Computes ea (vectorEncoding n) f
  | 0, _f, _ => congrComputes (constantComputes ea (vectorEncoding 0) Fin.elim0)
      (fun _a => funext (fun i => Fin.elim0 i))
  | n + 1, f, w =>
      recode (pairComputes (w 0)
        (assembleComputes ea n (fun a => Fin.tail (f a)) (fun i => w i.succ)))
        id (fun _ => rfl) (fun _ => rfl)

/-- Even fixed-field constants retain the literal canonical scalar/vector codec. -/
noncomputable def vectorConstantComputes {α : Type} (ea : Encoding α Bool) (n : ℕ)
    (v : Fin n → ℚ) : Computes ea (vectorEncoding n) (fun _ => v) :=
  constantComputes ea (vectorEncoding n) v

end Holant.Complexity.FixedFieldMachines
