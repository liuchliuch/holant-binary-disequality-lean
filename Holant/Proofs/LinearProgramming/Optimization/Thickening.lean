import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.Completion.PhaseGap
import Holant.Proofs.LinearProgramming.Foundation.Precision

/-!
An input-derived full-dimensional weak-feasibility target. Every equality and
box face is thickened by epsilon=1/(4*D_aux*(1+n*2^L)). Clipping and an explicit
phase-I lift prove that this thickened set is empty exactly when the ORIGINAL
LP is infeasible. A rational inner box is derived even for zero-dimensional
original faces. No interior radius or tolerance is supplied by the caller.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Thickening
open Codec
open scoped BigOperators
noncomputable section

def H (d : Raw) : ℕ := 2^InputBounds.size d
def C (d : Raw) : ℕ := 1+d.dimension*H d
def D (d : Raw) : ℕ := PhaseGap.denominator d
def epsilon (d : Raw) : ℚ := 1/(4*(D d:ℚ)*(C d:ℚ))
def radius (d : Raw) : ℚ := epsilon d/(2*(C d:ℚ))
def residual (d : Raw) (x : Fin d.dimension → ℚ) (i : Fin d.rowCount) : ℚ :=
  (∑ j, (d.coefficient i j:ℚ)*x j)-(d.constant i:ℚ)
def At (d : Raw) (eta : ℚ) (x : Fin d.dimension → ℚ) : Prop :=
  (∀ j, -eta≤x j ∧ x j≤1+eta) ∧ ∀ i, |residual d x i|≤eta
def clip (x : ℚ) : ℚ := max 0 (min 1 x)

theorem C_pos (d : Raw) : 0<C d := by unfold C; omega
theorem D_pos (d : Raw) : 0<D d := InputBounds.denominator_pos (PhaseMatrix.value d).val
theorem H_pos (d : Raw) : 0<H d := by unfold H; positivity
theorem epsilon_pos (d : Raw) : 0<epsilon d := by
  have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
  have hd : (0:ℚ)<D d := by exact_mod_cast D_pos d
  unfold epsilon; positivity
theorem radius_pos (d : Raw) : 0<radius d := by
  have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
  exact div_pos (epsilon_pos d) (by positivity)

theorem clip_box (x : ℚ) : 0≤clip x ∧ clip x≤1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem clip_error (eta x : ℚ) (he : 0≤eta) (hx : -eta≤x ∧ x≤1+eta) : |clip x-x|≤eta := by
  by_cases h0 : x≤0
  · have h1 : x≤1 := h0.trans (by norm_num)
    simp only [clip,min_eq_right h1,max_eq_left h0,zero_sub,abs_neg]
    rw [abs_of_nonpos h0]; linarith [hx.1]
  · by_cases h1 : 1≤x
    · simp only [clip,min_eq_left h1,max_eq_right (by norm_num : (0:ℚ)≤1)]
      rw [abs_of_nonpos (by linarith : 1-x≤0)]; linarith [hx.2]
    · simp [clip,min_eq_right (le_of_not_ge h1),max_eq_right (le_of_not_ge h0),he]

theorem row_distance (d : Raw) (x y : Fin d.dimension → ℚ) (eta : ℚ) (he : 0≤eta)
    (hxy : ∀ j, |y j-x j|≤eta) (i : Fin d.rowCount) :
    |residual d y i-residual d x i|≤(d.dimension:ℚ)*(H d:ℚ)*eta := by
  calc
    _ = |∑ j, (d.coefficient i j:ℚ)*(y j-x j)| := by
      congr 1
      simp [residual,mul_sub,Finset.sum_sub_distrib]
    _ ≤ ∑ j, |(d.coefficient i j:ℚ)| * |y j-x j| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun j => (d.coefficient i j:ℚ)*(y j-x j)) Finset.univ
    _ ≤ ∑ _j : Fin d.dimension, (H d:ℚ)*eta := by
      apply Finset.sum_le_sum
      intro j _
      have ha : |(d.coefficient i j:ℚ)|≤(H d:ℚ) := by exact_mod_cast InputBounds.coefficient_bound d i j
      exact mul_le_mul ha (hxy j) (abs_nonneg _) (by positivity)
    _ = _ := by simp [mul_assoc]

def lift (d : Raw) (x : Fin d.dimension → ℚ) (t : ℚ) : PhaseOne.Point d where
  original := x
  positive := fun i => max (residual d x i) 0/(PhaseOne.scale d:ℚ)
  negative := fun i => max (-residual d x i) 0/(PhaseOne.scale d:ℚ)
  slackPositive := fun i => t-max (residual d x i) 0/(PhaseOne.scale d:ℚ)
  slackNegative := fun i => t-max (-residual d x i) 0/(PhaseOne.scale d:ℚ)
  objective := t

theorem lift_feasible (d : Raw) (x : Fin d.dimension → ℚ) (t : ℚ)
    (hx : ∀ j, 0≤x j ∧ x j≤1) (ht : 0≤t ∧ t≤1)
    (hr : ∀ i, |residual d x i|≤(PhaseOne.scale d:ℚ)*t) : PhaseOne.Feasible d (lift d x t) := by
  have hM : (0:ℚ)<PhaseOne.scale d := by exact_mod_cast PhaseOne.scale_pos d
  have parts (i : Fin d.rowCount) :
      0≤max (residual d x i) 0/(PhaseOne.scale d:ℚ) ∧
      max (residual d x i) 0/(PhaseOne.scale d:ℚ)≤t ∧
      0≤max (-residual d x i) 0/(PhaseOne.scale d:ℚ) ∧
      max (-residual d x i) 0/(PhaseOne.scale d:ℚ)≤t := by
    have h := abs_le.mp (hr i)
    refine ⟨div_nonneg (le_max_right _ _) hM.le,?_,div_nonneg (le_max_right _ _) hM.le,?_⟩
    · apply (div_le_iff₀ hM).mpr; apply max_le <;> nlinarith [mul_nonneg hM.le ht.1]
    · apply (div_le_iff₀ hM).mpr; apply max_le <;> nlinarith [mul_nonneg hM.le ht.1]
  refine ⟨hx,?_,ht.1,ht.2,?_,?_,?_⟩
  · intro i
    have h := parts i
    dsimp [lift]
    constructor
    · exact h.1
    constructor
    · exact h.2.1.trans ht.2
    constructor
    · exact h.2.2.1
    constructor
    · exact h.2.2.2.trans ht.2
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · intro i
    change residual d x i=(PhaseOne.scale d:ℚ)*(_-_)
    by_cases h : 0≤residual d x i
    · simp only [lift,max_eq_left h,max_eq_right (neg_nonpos.mpr h)]
      field_simp [ne_of_gt hM] <;> ring
    · simp only [lift,max_eq_right (le_of_not_ge h),max_eq_left (neg_nonneg.mpr (le_of_not_ge h))]
      field_simp [ne_of_gt hM] <;> ring
  · intro i; dsimp [lift]; ring
  · intro i; dsimp [lift]; ring

theorem clipped_residual (d : Raw) (x : Fin d.dimension → ℚ) (hx : At d (epsilon d) x)
    (i : Fin d.rowCount) : |residual d (fun j => clip (x j)) i|≤1/(4*(D d:ℚ)) := by
  have hd : (0:ℚ)<D d := by exact_mod_cast D_pos d
  have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
  have he := epsilon_pos d
  have h := row_distance d x (fun j => clip (x j)) (epsilon d) he.le
    (fun j => clip_error _ _ he.le (hx.1 j)) i
  have ha := abs_add_le (residual d (fun j => clip (x j)) i-residual d x i) (residual d x i)
  have eq : (d.dimension:ℚ)*(H d:ℚ)*epsilon d+epsilon d=1/(4*(D d:ℚ)) := by
    unfold epsilon C
    push_cast
    field_simp [ne_of_gt hd,ne_of_gt hc] <;> ring
  rw [← eq]
  simpa only [sub_add_cancel] using ha.trans (add_le_add h (hx.2 i))

/-- An approximate thick point cannot exist for an infeasible original. The
contradiction uses the proved phase-I gap, not an exact-recovery oracle. -/
theorem nonempty_iff (d : Raw) : (∃ x, At d (epsilon d) x) ↔ ∃ x, Codec.Feasible d x := by
  constructor
  · rintro ⟨x,hx⟩
    by_contra hno
    have hd : (1:ℚ)≤D d := by exact_mod_cast (Nat.succ_le_iff.mpr (D_pos d))
    have hdp : (0:ℚ)<D d := by linarith
    have hm : (1:ℚ)≤PhaseOne.scale d := by exact_mod_cast (Nat.succ_le_iff.mpr (PhaseOne.scale_pos d))
    let t : ℚ := 1/(2*(D d:ℚ))
    have ht : 0≤t ∧ t≤1 := by
      refine ⟨by dsimp [t]; positivity,?_⟩
      dsimp [t]; apply (div_le_iff₀ (by positivity)).mpr; linarith
    have hr : ∀ i, |residual d (fun j => clip (x j)) i|≤(PhaseOne.scale d:ℚ)*t := by
      intro i
      apply (clipped_residual d x hx i).trans
      dsimp [t]
      apply (div_le_iff₀ (by positivity : (0:ℚ)<4*(D d:ℚ))).mpr
      field_simp [ne_of_gt hdp] <;> nlinarith
    have hp := lift_feasible d (fun j => clip (x j)) t (fun j => clip_box _) ht hr
    have hf := (PhaseMatrix.feasible_vector d _).mpr hp
    have hg := PhaseGap.infeasible_gap d hno _ hf
    simp only [PhaseMatrix.vector,PhaseMatrix.blocks,PhaseMatrix.objective,
      Fin.snoc_last,lift] at hg
    change 1/(D d:ℚ)≤t at hg
    dsimp [t] at hg
    have hc : 1/(2*(D d:ℚ))<1/(D d:ℚ) := by
      apply one_div_lt_one_div_of_lt hdp
      linarith
    exact (not_le_of_gt hc) hg
  · rintro ⟨x,hx⟩
    refine ⟨x,?_,?_⟩
    · intro j; have h := hx.2 j; have he := epsilon_pos d; constructor <;> linarith
    · intro i; simp [residual,hx.1 i,(epsilon_pos d).le]

theorem radius_small (d : Raw) : radius d≤epsilon d/2 := by
  have hc : (1:ℚ)≤C d := by exact_mod_cast (Nat.succ_le_iff.mpr (C_pos d))
  have he := epsilon_pos d
  unfold radius
  apply (div_le_iff₀ (by positivity : (0:ℚ)<2*(C d:ℚ))).mpr
  nlinarith

/-- A complete coordinate box, not relative interior in an assumed affine
hull. This remains valid when the original feasible set is a singleton. -/
theorem inner_box (d : Raw) (x y : Fin d.dimension → ℚ) (hx : Codec.Feasible d x)
    (hy : ∀ j, |y j-x j|≤radius d) : At d (epsilon d/2) y := by
  have he := epsilon_pos d
  have hr := radius_pos d
  have hs := radius_small d
  refine ⟨?_,?_⟩
  · intro j
    have hxy := abs_le.mp (hy j)
    have hbox := hx.2 j
    constructor <;> linarith
  · intro i
    have h := row_distance d x y (radius d) hr.le hy i
    have hz : residual d x i=0 := by simp [residual,hx.1 i]
    rw [hz,sub_zero] at h
    apply h.trans
    have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
    have hc' : (d.dimension:ℚ)*(H d:ℚ)≤(C d:ℚ) := by simp [C]
    have hb := mul_le_mul_of_nonneg_right hc' hr.le
    have eq : (C d:ℚ)*radius d=epsilon d/2 := by
      unfold radius; field_simp [ne_of_gt hc] <;> ring
    exact hb.trans_eq eq

theorem epsilon_small (d : Raw) : epsilon d≤1/4 := by
  have hd : (1:ℚ)≤D d := by exact_mod_cast (Nat.succ_le_iff.mpr (D_pos d))
  have hc : (1:ℚ)≤C d := by exact_mod_cast (Nat.succ_le_iff.mpr (C_pos d))
  have hm := mul_le_mul hd hc (by norm_num : (0:ℚ)≤1) (by linarith : (0:ℚ)≤D d)
  unfold epsilon
  apply (div_le_iff₀ (by positivity : (0:ℚ)<4*(D d:ℚ)*(C d:ℚ))).mpr
  nlinarith

theorem outer_box (d : Raw) (x : Fin d.dimension → ℚ) (hx : At d (epsilon d) x)
    (j : Fin d.dimension) : -1≤x j ∧ x j≤2 := by
  have h := hx.1 j
  have he := epsilon_small d
  constructor <;> linarith

theorem perturb_strong (d : Raw) (x y : Fin d.dimension → ℚ) (hx : At d (epsilon d/2) x)
    (he : ∀ j, |y j-x j|≤radius d) : At d (epsilon d) y := by
  have hs := radius_small d
  refine ⟨?_,?_⟩
  · intro j
    have hp := abs_le.mp (he j)
    have hb := hx.1 j
    constructor <;> linarith
  · intro i
    have h := row_distance d x y (radius d) (radius_pos d).le he i
    have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
    have hn : (d.dimension:ℚ)*(H d:ℚ)≤(C d:ℚ) := by simp [C]
    have hh := mul_le_mul_of_nonneg_right hn (radius_pos d).le
    have eq : (C d:ℚ)*radius d=epsilon d/2 := by
      unfold radius; field_simp [ne_of_gt hc] <;> ring
    rw [eq] at hh
    have ha := abs_add_le (residual d y i-residual d x i) (residual d x i)
    have hb := ha.trans (add_le_add (h.trans hh) (hx.2 i))
    simpa only [sub_add_cancel,add_halves] using hb

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Thickening
