import Holant.Proofs.LinearProgramming.Optimization.Thickening

/-!
Concrete finite first-violated-constraint separation for the derived thick LP.
The output normal and offset are literal original rows or signed unit rows.
Zero normals are handled by a proved empty-set rejection. This is a finite
algorithm with a mathematical correctness proof. Search.Scanner supplies its
physical scan, and Search.RoundedTermination proves the exhaustion bound.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Separation
open Codec Thickening
open scoped BigOperators
noncomputable section

abbrev Constraint (d : Raw) := (Fin d.dimension ⊕ Fin d.rowCount) × Bool
def normal (d : Raw) (c : Constraint d) (j : Fin d.dimension) : ℚ :=
  let a := match c.1 with
    | .inl k => if j=k then 1 else 0
    | .inr i => (d.coefficient i j:ℚ)
  if c.2 then a else -a
def base (d : Raw) (c : Constraint d) : ℚ :=
  match c.1 with
  | .inl _ => if c.2 then 1 else 0
  | .inr i => if c.2 then (d.constant i:ℚ) else -(d.constant i:ℚ)
def offset (d : Raw) (c : Constraint d) : ℚ := base d c+epsilon d
def lhs (d : Raw) (c : Constraint d) (x : Fin d.dimension → ℚ) : ℚ := ∑ j, normal d c j*x j
def constraints (d : Raw) : List (Constraint d) :=
  (List.finRange d.dimension).flatMap (fun j => [(.inl j,false),(.inl j,true)])++
  (List.finRange d.rowCount).flatMap (fun i => [(.inr i,false),(.inr i,true)])

theorem mem_constraints (d : Raw) (c : Constraint d) : c∈constraints d := by
  rcases c with ⟨j,b⟩
  cases j <;> cases b <;> simp [constraints,List.mem_flatMap]

theorem all_constraints (d : Raw) (x : Fin d.dimension → ℚ) :
    At d (epsilon d) x ↔ ∀ c : Constraint d, lhs d c x≤offset d c := by
  constructor
  · rintro ⟨hx,hr⟩ ⟨c,b⟩
    cases c with
    | inl j => cases b <;> simp [lhs,normal,offset,base] <;> linarith [hx j]
    | inr i =>
      have h := abs_le.mp (hr i)
      cases b <;> simp [lhs,normal,offset,base,Finset.sum_neg_distrib,neg_mul] <;>
        dsimp [Thickening.residual] at h <;> linarith
  · intro h
    refine ⟨?_,?_⟩
    · intro j
      have hl := h (.inl j,false)
      have hu := h (.inl j,true)
      simp [lhs,normal,offset,base] at hl hu
      constructor <;> linarith
    · intro i
      have hl := h (.inr i,false)
      have hu := h (.inr i,true)
      simp [lhs,normal,offset,base,Finset.sum_neg_distrib,neg_mul] at hl hu
      apply abs_le.mpr
      dsimp [Thickening.residual]
      constructor <;> linarith

def separate (d : Raw) (x : Fin d.dimension → ℚ) : Option (Constraint d) :=
  (constraints d).find? (fun c => decide (offset d c<lhs d c x))

theorem none_iff (d : Raw) (x : Fin d.dimension → ℚ) : separate d x=none ↔ At d (epsilon d) x := by
  rw [all_constraints]
  simp only [separate,List.find?_eq_none,decide_eq_true_eq,not_lt]
  exact ⟨fun h c => h c (mem_constraints d c),fun h c _ => h c⟩

theorem violated (d : Raw) (x : Fin d.dimension → ℚ) (c : Constraint d)
    (hc : separate d x=some c) : offset d c<lhs d c x := by
  change (constraints d).find? (fun z : Constraint d => decide (offset d z < lhs d z x)) = some c at hc
  exact of_decide_eq_true (List.find?_some
    (p := fun z : Constraint d => decide (offset d z < lhs d z x)) hc)

theorem central_cut (d : Raw) (x y : Fin d.dimension → ℚ) (c : Constraint d)
    (hc : separate d x=some c) (hy : At d (epsilon d) y) :
    (∑ j, normal d c j*(y j-x j))<0 := by
  have hv := violated d x c hc
  have hf := (all_constraints d y).mp hy c
  have he : (∑ j, normal d c j*(y j-x j))=lhs d c y-lhs d c x := by
    simp [lhs,mul_sub,Finset.sum_sub_distrib]
  rw [he]
  linarith

theorem normal_bound (d : Raw) (c : Constraint d) (j : Fin d.dimension) :
    |normal d c j|≤(H d:ℚ) := by
  have hh : (1:ℚ)≤H d := by exact_mod_cast (Nat.succ_le_iff.mpr (H_pos d))
  rcases c with ⟨c,b⟩
  cases c with
  | inl k =>
    cases b <;> by_cases hj : j=k <;>
      simp only [normal,hj,↓reduceIte,abs_neg,abs_one,abs_zero]
    all_goals first | exact hh | exact (by norm_num : (0 : ℚ) ≤ 1).trans hh
  | inr i =>
    have h : |(d.coefficient i j:ℚ)|≤(H d:ℚ) := by exact_mod_cast InputBounds.coefficient_bound d i j
    cases b <;> simpa [normal] using h

/-- The actual valid cut survives a perturbed query center as a shallow cut
with a quantified offset. The perturbed center need NOT be feasible. -/
theorem perturbed_cut (d : Raw) (x rounded y : Fin d.dimension → ℚ) (c : Constraint d)
    (hc : separate d rounded=some c) (hy : At d (epsilon d) y)
    (delta : ℚ) (hd : 0≤delta) (hx : ∀ j, |rounded j-x j|≤delta) :
    (∑ j, normal d c j*(y j-x j))≤(d.dimension:ℚ)*(H d:ℚ)*delta := by
  have cut := central_cut d rounded y c hc hy
  have hb : (∑ j, normal d c j*(rounded j-x j))≤(d.dimension:ℚ)*(H d:ℚ)*delta := by
    calc
      _ ≤ |∑ j, normal d c j*(rounded j-x j)| := le_abs_self _
      _ ≤ ∑ j, |normal d c j| * |rounded j-x j| := by
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
          (fun j => normal d c j*(rounded j-x j)) Finset.univ
      _ ≤ ∑ _j : Fin d.dimension, (H d:ℚ)*delta := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul (normal_bound d c j) (hx j) (abs_nonneg _) (by positivity)
      _ = _ := by simp [mul_assoc]
  have he : (∑ j, normal d c j*(y j-x j))=
      (∑ j, normal d c j*(y j-rounded j))+(∑ j, normal d c j*(rounded j-x j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  linarith

theorem zero_cut_reject (d : Raw) (x : Fin d.dimension → ℚ) (c : Constraint d)
    (hc : separate d x=some c) (hz : normal d c=0) : ¬∃ y, Codec.Feasible d y := by
  intro h
  obtain ⟨y,hy⟩ := (nonempty_iff d).mpr h
  have hs := central_cut d x y c hc hy
  simp [hz] at hs

/-- Dimension zero has a single query point. Its actual separation result
already decides original feasibility, including inconsistent constant rows. -/
theorem zero_dimension (d : Codec.Raw) (hd : d.dimension=0) :
    Separation.separate d (fun _ => 0)=none ↔ ∃ x, Codec.Feasible d x := by
  rw [Separation.none_iff,← Thickening.nonempty_iff]
  constructor
  · intro h; exact ⟨_,h⟩
  · rintro ⟨x,hx⟩
    have he : x=(fun _ => 0) := by
      funext j
      have := j.isLt
      omega
    simpa only [he] using hx


end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Separation
