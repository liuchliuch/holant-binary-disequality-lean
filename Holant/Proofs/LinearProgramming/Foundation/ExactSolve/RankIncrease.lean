import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.BasicPoint
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
The boundary move increases the rank of the actual active-row span, not merely
the number of recorded constraints. Its new coordinate row evaluates nonzero
on a direction annihilating every old active row and therefore cannot lie in
their span. This also handles redundant original rows and degenerate faces.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.RankIncrease
open Codec FaceMove BasicPoint
open scoped BigOperators
noncomputable section

def span (d : Raw) (x : Fin d.dimension → ℚ) :=
  Submodule.span ℚ (Set.range (rows d x).row)

def evaluation {n : ℕ} (v : Fin n → ℚ) : (Fin n → ℚ) →ₗ[ℚ] ℚ where
  toFun a := ∑ k, a k*v k
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by simp [mul_assoc,Finset.mul_sum]

theorem annihilates (d : Raw) (x v : Fin d.dimension → ℚ) (hv : Tangent d x v) :
    span d x ≤ LinearMap.ker (evaluation v) := by
  apply Submodule.span_le.mpr
  rintro a ⟨r,rfl⟩
  change ∑ k, rows d x r k * v k = 0
  exact congrFun ((rows_kernel d x v).mpr hv) r

theorem span_mono (d : Raw) (x y : Fin d.dimension → ℚ) (h : tightSet x ⊆ tightSet y) :
    span d x ≤ span d y := by
  apply Submodule.span_mono
  rintro a ⟨r,rfl⟩
  have ha : Active d y r.val := by
    rcases r with ⟨r,hr⟩
    cases r with
    | inl i => trivial
    | inr k => exact (mem_tightSet y k).mp (h ((mem_tightSet x k).mpr hr))
  exact ⟨⟨r.val,ha⟩,rfl⟩

theorem strict_span (d : Raw) (x v : Fin d.dimension → ℚ) (hv : Tangent d x v)
    (t : ℚ) (k : Fin d.dimension) (hk : v k ≠ 0) (hh : Tight (move x v t) k) :
    span d x < span d (move x v t) := by
  classical
  have hle := span_mono d x (move x v t) (old_tight d x v hv t)
  apply lt_iff_le_not_ge.mpr
  refine ⟨hle,?_⟩
  intro hrev
  let r : ActiveIndex d (move x v t) := ⟨.inr k,hh⟩
  have hmem : rows d (move x v t) r ∈ span d (move x v t) :=
    Submodule.subset_span ⟨r,rfl⟩
  have he := annihilates d x v hv (hrev hmem)
  apply hk
  simpa [LinearMap.mem_ker,evaluation,rows,r,InputBounds.row] using he

theorem rank_increases (d : Raw) (x v : Fin d.dimension → ℚ) (hv : Tangent d x v)
    (t : ℚ) (k : Fin d.dimension) (hk : v k ≠ 0) (hh : Tight (move x v t) k) :
    Module.finrank ℚ (span d x) < Module.finrank ℚ (span d (move x v t)) :=
  Submodule.finrank_lt_finrank_of_lt (strict_span d x v hv t k hk hh)

theorem exists_rank_increase (d : Raw) (x : Fin d.dimension → ℚ) (hx : Feasible d x)
    (hn : ¬ Rigid d x) (j : Fin d.dimension) :
    ∃ y, Feasible d y ∧ x j ≤ y j ∧
      Module.finrank ℚ (span d x) < Module.finrank ℚ (span d y) := by
  classical
  have hd : ∃ v, Tangent d x v ∧ v ≠ 0 := by
    by_contra hnone
    apply hn
    intro v hv
    by_contra hv0
    exact hnone ⟨v,hv,hv0⟩
  obtain ⟨v,hv,hv0⟩ := hd
  obtain ⟨w,hw,hw0,hwj⟩ := orient d x v hv hv0 j
  obtain ⟨t,k,ht,hk,hy,hh,-,-⟩ := first_boundary d x w hx hw hw0
  refine ⟨move x w t,hy,?_,rank_increases d x w hw t k hk hh⟩
  dsimp [move]
  exact le_add_of_nonneg_right (mul_nonneg ht.le hwj)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.RankIncrease
