import Holant.Projective.BoundedTorsion.PGL
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite


namespace Holant.LocalDrafts.FinitePGL2.Stabilization

open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {L E : Type*} [Field L] [Field E]

def pglExtend (f : L →+* E) : PGL2 L →* PGL2 E :=
  QuotientGroup.lift (scalarSubgroup L)
    ((pglMk E).comp (Matrix.GeneralLinearGroup.map f)) (by
      rintro U ⟨c, rfl⟩
      change pglMk E (Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar Bool c)) = 1
      rw [Matrix.GeneralLinearGroup.map_scalar]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨Units.map f c, rfl⟩)

@[simp] theorem pglExtend_mk (f : L →+* E) (U : Matrix.GeneralLinearGroup Bool L) :
    pglExtend f (pglMk L U) = pglMk E (Matrix.GeneralLinearGroup.map f U) := rfl

theorem pglExtend_injective (f : L →+* E) : Function.Injective (pglExtend f) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h U =>
    induction r using Quotient.inductionOn with
    | h V =>
      intro he
      apply pglMk_eq_iff_projectiveClass_eq.mpr
      apply projectiveClass_map_injective f (B := (V : Binary))
      · intro hz
        exact V.det_ne_zero (by rw [hz, Matrix.det_zero])
      · exact pglMk_eq_iff_projectiveClass_eq.mp he

theorem pglExtend_order (f : L →+* E) (q : PGL2 L) :
    orderOf (pglExtend f q) = orderOf q :=
  orderOf_injective (pglExtend f) (pglExtend_injective f) q

theorem pglExtend_card (f : L →+* E) (H : Subgroup (PGL2 L)) :
    Nat.card (H.map (pglExtend f)) = Nat.card H :=
  Subgroup.card_map_of_injective (pglExtend_injective f)

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
