import Mathlib.Data.Fin.VecNotation

namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionFullSupport
open Function
/-- Coordinate-edge invariance implies global invariance on a Boolean cube. -/
theorem constant_of_coordinates {B : Type*} : ∀n : ℕ, ∀R : (Fin n → Bool) → B,
    (∀i x,R (update x i false)=R (update x i true)) → ∀x y,R x=R y := by
  intro n
  induction n with
  | zero => intro R h x y; exact congrArg R (Subsingleton.elim x y)
  | succ n ih =>
    intro R h x y
    have ht (b : Bool) : R (Fin.cons b (Fin.tail x))=R (Fin.cons b (Fin.tail y)) := by
      apply ih (fun z => R (Fin.cons b z))
      intro i z
      simpa only [Fin.cons_update] using h i.succ (Fin.cons b z)
    have hh : R (Fin.cons false (Fin.tail x))=R (Fin.cons true (Fin.tail x)) := by
      simpa only [Fin.update_cons_zero] using h 0 (Fin.cons false (Fin.tail x))
    calc
      R x=R (Fin.cons (x 0) (Fin.tail x)) := congrArg R (Fin.cons_self_tail x).symm
      _=R (Fin.cons (y 0) (Fin.tail x)) := by cases x 0 <;> cases y 0 <;> first | rfl | exact hh | exact hh.symm
      _=R (Fin.cons (y 0) (Fin.tail y)) := ht (y 0)
      _=R y := congrArg R (Fin.cons_self_tail y)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionFullSupport
