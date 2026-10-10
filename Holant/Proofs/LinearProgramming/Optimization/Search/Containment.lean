import Holant.Proofs.LinearProgramming.Optimization.Separation
import Holant.Proofs.LinearProgramming.Optimization.Search.Projection

/-!
Containment for the actual original-input separation cut and rational update.
All points and their constructed inverse images here are rational. The initial
factor is derived from dimension and contains the entire thickened target.
This establishes an update invariant, not a finite-volume exhaustion theorem
or a bound on the bit length of repeatedly updated factors.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Containment
open FactorUpdate Projection
open scoped BigOperators Matrix

def Contains {n : ℕ} (s : State n) (x : Vec n) : Prop :=
  ∃ y : Vec n, square y≤1 ∧ x=s.center+s.factor.mulVec y

def start (n : ℕ) : State n := { center := 0, factor := (2*((n:ℚ)+1)) • (1 : Mat n) }

theorem start_nonsingular (n : ℕ) : (start n).factor.det≠0 := by
  simp only [start,Matrix.det_smul,Matrix.det_one,mul_one,Fintype.card_fin]
  apply pow_ne_zero
  positivity

theorem pulled_nonzero {n : ℕ} (s : State n) (g : Vec n)
    (hR : s.factor.det≠0) (hg : g≠0) : pulled s g≠0 := by
  have hunit : IsUnit s.factor.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (by simpa using hR))
  intro h
  apply hg
  apply Matrix.mulVec_injective_of_isUnit hunit
  simpa only [pulled,Matrix.mulVec_zero] using h

theorem halfspace_contains {n : ℕ} (hn : 2≤n) (s : State n) (g x : Vec n)
    (hR : s.factor.det≠0) (hg : g≠0) (hx : Contains s x)
    (hcut : g ⬝ᵥ (x-s.center)≤0) : Contains (update s g) x := by
  obtain ⟨y,hy,hxy⟩ := hx
  let v := pulled s g
  have hv : v≠0 := pulled_nonzero s g hR hg
  have hc : v ⬝ᵥ y≤0 := by
    rw [hxy,add_sub_cancel_left] at hcut
    simpa only [v,pulled,Matrix.mulVec_transpose,Matrix.dotProduct_mulVec] using hcut
  obtain ⟨z,hz,hm⟩ := half_ball_covered hn v y hv hy hc
  refine ⟨z,hz,?_⟩
  change x=s.center-s.factor.mulVec (shift v • v)+(s.factor*transform v).mulVec z
  rw [←Matrix.mulVec_mulVec,hm,Matrix.mulVec_add]
  rw [hxy]
  abel

theorem start_contains (d : Codec.Raw) (x : Vec d.dimension)
    (hx : Thickening.At d (Thickening.epsilon d) x) : Contains (start d.dimension) x := by
  let R : ℚ := 2*((d.dimension:ℚ)+1)
  have hR : 0<R := by dsimp [R]; positivity
  have hb := Thickening.outer_box d x hx
  have hs : square x≤4*(d.dimension:ℚ) := by
    calc
      _ ≤ ∑ _j : Fin d.dimension, (4:ℚ) := by
        apply Finset.sum_le_sum
        intro j _
        obtain ⟨hl,hu⟩ := hb j
        nlinarith
      _ = _ := by simp; ring
  have hsize : 4*(d.dimension:ℚ)≤R^2 := by
    dsimp [R]
    nlinarith [sq_nonneg (d.dimension:ℚ)]
  refine ⟨(1/R) • x,?_,?_⟩
  · rw [square_smul]
    have he : (1/R)^2*square x=square x/R^2 := by ring
    rw [he]
    exact (div_le_one (sq_pos_of_pos hR)).mpr (hs.trans hsize)
  · change x=0+(R • (1 : Mat d.dimension)).mulVec ((1/R) • x)
    simp only [zero_add,Matrix.smul_mulVec,Matrix.one_mulVec,smul_smul]
    rw [mul_one_div_cancel (ne_of_gt hR),one_smul]

/-- Preserve every target point under the actual returned constraint. The
normal is not supplied as an arbitrary allegedly valid separator. -/
theorem actual_cut_contains (d : Codec.Raw) (hn : 2≤d.dimension)
    (s : State d.dimension) (c : Separation.Constraint d)
    (hR : s.factor.det≠0) (hc : Separation.separate d s.center=some c)
    (hg : Separation.normal d c≠0)
    (hold : ∀ x, Thickening.At d (Thickening.epsilon d) x → Contains s x) :
    ∀ x, Thickening.At d (Thickening.epsilon d) x → Contains (update s (Separation.normal d c)) x := by
  intro x hx
  apply halfspace_contains hn s (Separation.normal d c) x hR hg (hold x hx)
  exact (Separation.central_cut d s.center x c hc hx).le

theorem actual_cut_progress (d : Codec.Raw) (hn : 2≤d.dimension)
    (s : State d.dimension) (c : Separation.Constraint d)
    (hR : s.factor.det≠0) (hg : Separation.normal d c≠0) :
    (update s (Separation.normal d c)).factor.det≠0 ∧
    |(update s (Separation.normal d c)).factor.det|≤
      |s.factor.det| * Scales.contraction d.dimension := by
  have hv := pulled_nonzero s (Separation.normal d c) hR hg
  exact ⟨update_preserves_nonsingular hn s _ hR hv,update_contracts hn s _ hv⟩

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Containment
