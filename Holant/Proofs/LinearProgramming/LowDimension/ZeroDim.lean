import Holant.Proofs.LinearProgramming.Interface

/-! Zero-dimensional bounded rational feasibility.
Adapted from the frozen reference Zero.lean, retaining its literal RHS scan.
This module proves semantics only; the physical machine is supplied separately.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.LowDimension.ZeroDim
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open scoped BigOperators

def checks (d : Codec.Raw) : List Bool :=
  (List.range d.rowCount).map (fun i => decide (d.rhs.getD i 0 = 0))
def accepted (d : Codec.Raw) : Bool := (checks d).all id
def value (d : Codec.Raw) : Option (List ℚ) := if accepted d then some [] else none

theorem accepted_true (d : Codec.Raw) :
    accepted d = true ↔ ∀ i : Fin d.rowCount, d.constant i = 0 := by
  simp only [accepted, checks, List.all_map, List.all_eq_true, Function.comp_def,
    id_eq, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h i; exact h i.val i.isLt
  · intro h i hi; exact h ⟨i, hi⟩

theorem feasible_iff (d : Codec.Raw) (hn : d.dimension = 0) (x : Fin d.dimension → ℚ) :
    Codec.Feasible d x ↔ accepted d = true := by
  haveI : IsEmpty (Fin d.dimension) := by rw [hn]; infer_instance
  rw [accepted_true]
  constructor
  · intro hx i
    have he := hx.1 i
    have hz : (∑ j : Fin d.dimension, (d.coefficient i j : ℚ)*x j) = 0 :=
      Finset.sum_eq_zero (fun j _ => isEmptyElim j)
    rw [hz] at he
    exact_mod_cast he.symm
  · intro h
    refine ⟨?_, fun j => isEmptyElim j⟩
    intro i
    simp [h i]

theorem none_iff (d : Codec.Raw) (hn : d.dimension = 0) :
    value d = none ↔ ¬ ∃ x, Codec.Feasible d x := by
  have he : (∃ x, Codec.Feasible d x) ↔ accepted d = true := by
    constructor
    · rintro ⟨x, hx⟩; exact (feasible_iff d hn x).mp hx
    · intro h; exact ⟨fun _ => 0, (feasible_iff d hn _).mpr h⟩
  rw [he]
  cases h : accepted d <;> simp [value, h]
theorem response (d : Codec.Raw) (hn : d.dimension = 0) : Codec.Response d (value d) := by
  cases h : accepted d
  · simpa [value, h, Codec.Response] using (none_iff d hn).mp (by simp [value, h])
  · simp only [value, h,  ↓reduceIte, Codec.Response]
    change [].length = d.dimension ∧ Codec.Feasible d (Codec.point d [])
    exact ⟨by simp [hn], (feasible_iff d hn _).mpr h⟩

/-- No coordinate can occur in a zero-dimensional common-support obligation. -/
theorem maximalSupport (d : Codec.Input) (hn : d.val.dimension = 0)
    (xs : List ℚ) : ∀ j : Fin d.val.dimension,
      0 < Codec.point d.val xs j ↔
        Holant.LocalDrafts.RemoteWork.RationalLP.PositiveAt d j := by
  intro j
  have hj := j.isLt
  omega

end Holant.LocalDrafts.RemoteWork.RationalLP.LowDimension.ZeroDim
