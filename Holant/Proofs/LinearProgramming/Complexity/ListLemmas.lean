import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Holant.Complexity.FramedEncoding
import Mathlib.Tactic.Linarith

/-! Shared semantic facts for the physically tabulated rational lists.
These lemmas do not select a point or claim a machine running time. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.DensePrograms

/-- A dynamic unary range and a finite-function table contain identical entries. -/
theorem range_map {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Default-valued reads agree with the original finite table inside its bounds. -/
@[simp] theorem getD_ofFn {A : Type} {n : ℕ} (f : Fin n → A) (j : Fin n) (a : A) :
    (List.ofFn f).getD j.val a = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using j.isLt)]
  simp

end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.DensePrograms

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.ListBounds
open Computability Holant.Complexity

/-- Count each list tag, each doubled frame bit, and the final terminator. -/
theorem framed_length {A : Type} (e : Encoding A Bool) (xs : List A) (B : ℕ)
    (h : ∀ x ∈ xs, (e.encode x).length ≤ B) :
    ((framedListEncoding e).encode xs).length ≤ (2 * B + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [framedListEncoding, framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [framedListEncoding, framedListEncode, List.length_cons, List.length_append,
      Holant.Algebraic.frame_length] at ht ⊢
    nlinarith

end Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.ListBounds
