import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.FaceMove
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open Holant.LocalDrafts.TraversalCompletion.RationalLP

/-! Rational LP foundation adapted into the exclusive task namespace.
Existence of a rational basic point without an optimal-point premise. Boundary
motion strictly increases the set of tight coordinates, hence terminates in
at most n moves. A terminal point has no common null direction, so its actual
active rows span the coordinate space. Basis selection below is a semantic
existence proof only: no vertex enumeration or polynomial pivot claim.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.BasicPoint
open Codec FaceMove Matrix
open scoped BigOperators
noncomputable section

theorem tight_card_le (d : Raw) (x : Fin d.dimension → ℚ) : (tightSet x).card ≤ d.dimension := by
  simpa using Finset.card_le_univ (s := tightSet x)

theorem exists_rigid_above (d : Raw) (j : Fin d.dimension) (x : Fin d.dimension → ℚ)
    (hx : Feasible d x) : ∃ y, Feasible d y ∧ x j ≤ y j ∧ Rigid d y := by
  classical
  have aux : ∀ r, ∀ x : Fin d.dimension → ℚ, Feasible d x →
      d.dimension - (tightSet x).card = r →
      ∃ y, Feasible d y ∧ x j ≤ y j ∧ Rigid d y := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro x hx hr
      by_cases hg : Rigid d x
      · exact ⟨x,hx,le_rfl,hg⟩
      · have hd : ∃ v, Tangent d x v ∧ v ≠ 0 := by
          by_contra hnone
          apply hg
          intro v hv
          by_contra hn
          exact hnone ⟨v,hv,hn⟩
        obtain ⟨v,hv,hn⟩ := hd
        obtain ⟨w,hw,hwn,hwj⟩ := orient d x v hv hn j
        obtain ⟨t,k,ht,hk,hy,hhit,hnot,hsub⟩ := first_boundary d x w hx hw hwn
        have hc := Finset.card_lt_card hsub
        have hbound := tight_card_le d (move x w t)
        have hlt : d.dimension-(tightSet (move x w t)).card < r := by omega
        obtain ⟨y,hy',hjy,hg'⟩ := ih _ hlt (move x w t) hy rfl
        refine ⟨y,hy',le_trans ?_ hjy,hg'⟩
        have hm := mul_nonneg ht.le hwj
        dsimp [move]
        linarith
  exact aux _ x hx rfl

theorem exists_rigid (d : Raw) (x : Fin d.dimension → ℚ) (hx : Feasible d x) :
    ∃ y, Feasible d y ∧ Rigid d y := by
  by_cases hz : d.dimension = 0
  · refine ⟨x,hx,?_⟩
    intro v _
    funext k
    have hk := k.isLt
    omega
  · obtain ⟨y,hy,_,hr⟩ := exists_rigid_above d ⟨0,by omega⟩ x hx
    exact ⟨y,hy,hr⟩

def Active (d : Raw) (x : Fin d.dimension → ℚ) : InputBounds.Row d → Prop
  | .inl _ => True
  | .inr k => Tight x k

abbrev ActiveIndex (d : Raw) (x : Fin d.dimension → ℚ) := {r : InputBounds.Row d // Active d x r}

def rows (d : Raw) (x : Fin d.dimension → ℚ) :
    Matrix (ActiveIndex d x) (Fin d.dimension) ℚ := fun r k => (InputBounds.row d r.val k : ℚ)

theorem rows_kernel (d : Raw) (x v : Fin d.dimension → ℚ) :
    rows d x *ᵥ v = 0 ↔ Tangent d x v := by
  classical
  constructor
  · intro h
    constructor
    · intro i
      simpa [rows,InputBounds.row,Matrix.mulVec,dotProduct] using congrFun h ⟨.inl i,trivial⟩
    · intro k hk
      simpa [rows,InputBounds.row,Matrix.mulVec,dotProduct] using congrFun h ⟨.inr k,hk⟩
  · intro h
    ext r
    rcases r with ⟨i,hi⟩
    cases i with
    | inl i => simpa [rows,InputBounds.row,Matrix.mulVec,dotProduct] using h.1 i
    | inr k => simpa [rows,InputBounds.row,Matrix.mulVec,dotProduct] using h.2 k hi

theorem rows_rank (d : Raw) (x : Fin d.dimension → ℚ) (hx : Rigid d x) :
    (rows d x).rank = d.dimension := by
  classical
  have hk : LinearMap.ker (rows d x).mulVecLin = ⊥ :=
    Matrix.ker_mulVecLin_eq_bot_iff.mpr (fun v hv => hx v ((rows_kernel d x v).mp hv))
  have hi := LinearMap.ker_eq_bot.mp hk
  simpa [Matrix.rank] using LinearMap.finrank_range_of_inj hi

/-- The selected rows really are original equalities or tight coordinate rows. -/
theorem exists_basis (d : Raw) (x : Fin d.dimension → ℚ) (hx : Rigid d x) :
    ∃ select : Fin d.dimension → InputBounds.Row d,
      (∀ i, Active d x (select i)) ∧ (InputBounds.matrix d select).det ≠ 0 := by
  classical
  have hr : Module.finrank ℚ (Submodule.span ℚ (Set.range (rows d x).row)) = d.dimension := by
    rw [← Matrix.rank_eq_finrank_span_row, rows_rank d x hx]
  obtain ⟨f,hmem,hspan,hlin⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range (rows d x).row)
  let g : Fin d.dimension → (Fin d.dimension → ℚ) := fun i => f (Fin.cast hr.symm i)
  have hmem' : ∀ i, g i ∈ Set.range (rows d x).row := fun i => hmem _
  choose index hindex using hmem'
  let select : Fin d.dimension → InputBounds.Row d := fun i => (index i).val
  have hli : LinearIndependent ℚ g :=
    hlin.comp (Fin.cast hr.symm) (Fin.cast_injective _)
  have he : DeterminantGap.castMatrix (InputBounds.matrix d select) = g := by
    funext i k
    exact congrFun (hindex i) k
  have hd : (DeterminantGap.castMatrix (InputBounds.matrix d select)).det ≠ 0 := by
    have hm : LinearIndependent ℚ (DeterminantGap.castMatrix (InputBounds.matrix d select)).row := by
      simpa only [he,Matrix.row] using hli
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hm)).ne_zero
  refine ⟨select,fun i => (index i).property,?_⟩
  intro hz
  apply hd
  simpa [DeterminantGap.castMatrix,← Int.cast_det] using congrArg (fun z : ℤ => (z : ℚ)) hz

def rightSide (d : Raw) (x : Fin d.dimension → ℚ) : InputBounds.Row d → ℤ
  | .inl i => d.constant i
  | .inr k => if x k = 1 then 1 else 0

theorem active_equation (d : Raw) (x : Fin d.dimension → ℚ) (hx : Feasible d x)
    (r : InputBounds.Row d) (hr : Active d x r) :
    ∑ k, (InputBounds.row d r k : ℚ)*x k = (rightSide d x r : ℚ) := by
  cases r with
  | inl i => exact hx.1 i
  | inr k =>
    rcases hr with h0 | h1
    · simp [InputBounds.row,rightSide,h0]
    · simp [InputBounds.row,rightSide,h1]

theorem basis_system (d : Raw) (x : Fin d.dimension → ℚ) (hx : Feasible d x)
    (select : Fin d.dimension → InputBounds.Row d) (ha : ∀ i, Active d x (select i)) :
    DeterminantGap.castMatrix (InputBounds.matrix d select) *ᵥ x =
      fun i => (rightSide d x (select i) : ℚ) := by
  funext i
  exact active_equation d x hx (select i) (ha i)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.BasicPoint
