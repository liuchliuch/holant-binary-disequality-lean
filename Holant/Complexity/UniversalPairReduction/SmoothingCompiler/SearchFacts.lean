import Holant.Complexity.UniversalPairReduction.Smoothing

/-! Exact first-hit and deletion identities for the original unique-label stream. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open FixedGadgetSubstitution
set_option maxRecDepth 8192
set_option Elab.async false
variable {A : Type}

theorem complement_filter_of_empty (p : A → Bool) (xs : List A)
    (h : xs.filter p = []) : xs.filter (fun x => !(p x)) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a with
    | false =>
      have ht : xs.filter p = [] := by simpa only [List.filter_cons,hp,Bool.false_eq_true,reduceIte] using h
      simpa [hp] using congrArg (List.cons a) (ih ht)
    | true => simp [hp] at h

theorem filter_eq_search (p : A → Bool) (xs : List A)
    (h : (xs.filter p).length ≤ 1) :
    xs.filter p = (xs[xs.findIdx p]?).toList := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a with
    | false =>
      have ht : (xs.filter p).length ≤ 1 := by simpa [hp] using h
      simpa [List.findIdx_cons,hp] using ih ht
    | true =>
      have hz : xs.filter p = [] := List.length_eq_zero_iff.mp (by simpa [hp] using h)
      simp [List.findIdx_cons,hp,hz]

theorem complement_filter_eq_erase (p : A → Bool) (xs : List A)
    (h : (xs.filter p).length ≤ 1) :
    xs.filter (fun x => !(p x)) = xs.eraseIdx (xs.findIdx p) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a with
    | false =>
      have ht : (xs.filter p).length ≤ 1 := by simpa [hp] using h
      simpa [List.findIdx_cons,hp] using congrArg (List.cons a) (ih ht)
    | true =>
      have hz : xs.filter p = [] := List.length_eq_zero_iff.mp (by simpa [hp] using h)
      simpa [List.findIdx_cons,hp] using complement_filter_of_empty p xs hz

theorem found_label (s : ℕ) (rows : List RawVertex) (row : RawVertex)
    (h : rows[rows.findIdx (fun row => row.1 == s)]? = some row) : row.1 = s := by
  have ht : rows.findIdx (fun row => row.1 == s) < rows.length := by
    exact List.getElem?_eq_some_iff.mp h |>.1
  have hp := @List.findIdx_getElem _ (fun row : RawVertex => row.1 == s) rows ht
  have he := List.getElem?_eq_some_iff.mp h |>.2
  simpa [he] using hp

theorem found_binary (s : ℕ) (arity : ℕ → ℕ) (r : Input s arity) (row : RawVertex)
    (h : r.val.vertices[r.val.vertices.findIdx (fun row => row.1 == s)]? = some row) :
    row.2.length = 2 := by
  have hi := List.getElem?_eq_some_iff.mp h
  let v : Fin r.val.vertices.length := ⟨_,hi.1⟩
  have hw := (r.property.1.1 v).2
  have he : r.val.vertices.get v = row := hi.2
  rw [he,found_label s r.val.vertices row h] at hw
  simpa [extendedArity] using hw

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
