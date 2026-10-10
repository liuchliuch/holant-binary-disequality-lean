import Holant.Realization
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Data.Set.Finite.Basic

/-! A scope obstruction for literal scalar-universal finite retention.
The frozen deck has finitely many chosen actual representatives and literal
raw keys. It cannot literally retain every unit multiple of any nonzero table
over the original characteristic-zero field. Scalar transport is a separate
statement and does not require adding that infinite literal orbit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceScalarScope
open Holant
variable {L : Type*} [Field L] [CharZero L] {n : ℕ}

/-- Even positive integer scalar multiples already form an infinite orbit. -/
theorem positive_scales_injective (f : Signature L n) (hf : f ≠ 0) :
    Function.Injective (fun k : ℕ => ((k + 1 : ℕ) : L) • f) := by
  intro i j hij
  have h : ((i + 1 : ℕ) : L) = ((j + 1 : ℕ) : L) := smul_left_injective L hf hij
  exact Nat.add_right_cancel (Nat.cast_injective h)

theorem finite_tables_cannot_retain_all_nonzero_scalars
    (F : Set (Signature L n)) (finite : F.Finite) (f : Signature L n) (hf : f ≠ 0) :
    ¬ ∀ c : L, c ≠ 0 → c • f ∈ F := by
  intro allScales
  have orbit : (Set.range (fun k : ℕ => ((k + 1 : ℕ) : L) • f)).Infinite :=
    Set.infinite_range_of_injective (positive_scales_injective f hf)
  apply orbit
  apply finite.subset
  rintro _ ⟨k, rfl⟩
  exact allScales _ (Nat.cast_ne_zero.mpr (by simp))

/-- Literal all-unit-scaled retention is likewise impossible. -/
theorem finite_tables_cannot_retain_all_unit_scalars
    (F : Set (Signature L n)) (finite : F.Finite) (f : Signature L n) (hf : f ≠ 0) :
    ¬ ∀ c : Lˣ, (c : L) • f ∈ F := by
  intro allUnits
  apply finite_tables_cannot_retain_all_nonzero_scalars F finite f hf
  intro c hc
  exact allUnits (Units.mk0 c hc)

/-- The same obstruction holds for a finite mixed-arity literal family. -/
theorem finite_family_cannot_retain_all_unit_scalars
    (F : SignatureFamily L) (finite : F.Finite) (f : Signature L n) (hf : f ≠ 0) :
    ¬ ∀ c : Lˣ, (⟨n, (c : L) • f⟩ : AnySignature L) ∈ F := by
  intro allUnits
  let fixedArity : Set (Signature L n) :=
    (fun g : Signature L n => (⟨n, g⟩ : AnySignature L)) ⁻¹' F
  have finiteFixed : fixedArity.Finite := finite.preimage sigma_mk_injective.injOn
  exact finite_tables_cannot_retain_all_unit_scalars fixedArity finiteFixed f hf allUnits

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceScalarScope
end
