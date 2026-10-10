import Holant.Tractable.AffineOperations


namespace Holant.LocalDrafts.Tractability.AffineMachine.ListSums

open scoped BigOperators

theorem filter_sum {A R : Type} [AddMonoid R] (xs : List A) (p : A → Bool) (f : A → R) :
    ((xs.filter p).map f).sum = (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : p x <;> simp [hx, ih]

theorem filterMap_sum {A B R : Type} [AddMonoid R] (xs : List A) (g : A → Option B) (f : B → R) :
    ((xs.filterMap g).map f).sum = (xs.map (fun x => (g x).elim 0 f)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : g x <;> simp [hx, ih]

theorem flatMap_sum {A B R : Type} [AddMonoid R] (xs : List A) (g : A → List B) (f : B → R) :
    ((xs.flatMap g).map f).sum = (xs.map (fun x => ((g x).map f).sum)).sum := by
  induction xs <;> simp_all

@[simp] theorem finRange_sum {R : Type} [AddCommMonoid R] {n : ℕ} (f : Fin n → R) :
    ((List.finRange n).map f).sum = ∑ j, f j := by
  simpa only [List.ofFn_eq_map] using (List.sum_ofFn (f := f))

end Holant.LocalDrafts.Tractability.AffineMachine.ListSums
