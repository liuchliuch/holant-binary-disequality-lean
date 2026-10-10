import Holant.Proofs.LinearProgramming.Optimization.Search.Trajectory
import Holant.Proofs.LinearProgramming.Optimization.RadiusBudget
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
Input-derived lower determinant bound for the actual unrounded trajectory.
Only the original feasible point and its n one-coordinate perturbations are
used in the proof; no interior ball or matrix-size certificate is an input.
The nonsingular inverse occurs in proofs only, not in the running update.
This closes the geometric size obstruction needed for finite search budgets;
it does not bound canonical denominators of repeatedly updated factors.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.InverseBounds
open FactorUpdate Containment
open scoped BigOperators Matrix
noncomputable section

def exponent (d : Codec.Raw) : ℕ :=
  d.dimension*d.dimension+(RadiusBudget.exponent d+1)*d.dimension

theorem ball_coordinate {n : ℕ} (y : Vec n) (hy : square y≤1) (i : Fin n) : |y i|≤1 := by
  have hs : y i^2≤square y :=
    Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  apply abs_le.mpr
  constructor <;> nlinarith

theorem inverse_coordinate {n : ℕ} (s : State n) (x : Vec n)
    (hR : s.factor.det≠0) (hx : Contains s x) (i : Fin n) :
    |(s.factor⁻¹.mulVec (x-s.center)) i|≤1 := by
  obtain ⟨y,hy,hxy⟩ := hx
  have hunit : IsUnit s.factor.det := isUnit_iff_ne_zero.mpr hR
  have he : s.factor⁻¹.mulVec (x-s.center)=y := by
    rw [hxy,add_sub_cancel_left,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit,Matrix.one_mulVec]
  rw [he]
  exact ball_coordinate y hy i

/-- Two actually contained points bound a whole inverse column. The factor 2
allows a simpler proof than a symmetric endpoint construction. -/
theorem inverse_entry {n : ℕ} (s : State n) (x : Vec n) (rho : ℚ)
    (hr : 0<rho) (hR : s.factor.det≠0) (hx : Contains s x)
    (j : Fin n) (hp : Contains s (x+Pi.single j rho)) (i : Fin n) :
    |s.factor⁻¹ i j|≤2/rho := by
  have h0 := inverse_coordinate s x hR hx i
  have h1 := inverse_coordinate s (x+Pi.single j rho) hR hp i
  have he : (s.factor⁻¹.mulVec (x+Pi.single j rho-s.center)) i-
      (s.factor⁻¹.mulVec (x-s.center)) i=s.factor⁻¹ i j*rho := by
    have hv : (x+Pi.single j rho-s.center)-(x-s.center)=Pi.single j rho := by abel
    have hm := congrFun (Matrix.mulVec_sub s.factor⁻¹
      (x+Pi.single j rho-s.center) (x-s.center)) i
    rw [hv,Matrix.mulVec_single] at hm
    change s.factor⁻¹ i j*rho=
      (s.factor⁻¹.mulVec (x+Pi.single j rho-s.center)) i-
      (s.factor⁻¹.mulVec (x-s.center)) i at hm
    exact hm.symm
  have hb : |s.factor⁻¹ i j*rho|≤2 := by
    rw [← he]
    exact (abs_sub _ _).trans (by linarith)
  rw [abs_mul,abs_of_pos hr] at hb
  exact (le_div_iff₀ hr).mpr hb

theorem inner_full (d : Codec.Raw) (x y : Vec d.dimension) (hx : Codec.Feasible d x)
    (hy : ∀ j, |y j-x j|≤Thickening.radius d) :
    Thickening.At d (Thickening.epsilon d) y := by
  obtain ⟨hb,he⟩ := Thickening.inner_box d x y hx hy
  have hp := Thickening.epsilon_pos d
  refine ⟨?_,?_⟩
  · intro j
    obtain ⟨hl,hu⟩ := hb j
    constructor <;> linarith
  · intro i
    exact (he i).trans (by linarith)

/-- No assumed all-states inverse bound: use the actual containment invariant
and the radius computed from the ORIGINAL LP input. -/
theorem actual_inverse_entry (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hf : ∃ x, Codec.Feasible d x) (i j : Fin d.dimension) :
    |(Trajectory.run d k).factor⁻¹ i j|≤(2^(RadiusBudget.exponent d+1):ℕ) := by
  obtain ⟨x,hx⟩ := hf
  obtain ⟨hR,hcontains⟩ := Trajectory.invariant d hn k
  have hr := Thickening.radius_pos d
  have hbase : Contains (Trajectory.run d k) x :=
    hcontains x (inner_full d x x hx (fun l => by simp [hr.le]))
  have hperturb : Contains (Trajectory.run d k) (x+Pi.single j (Thickening.radius d)) := by
    apply hcontains
    apply inner_full d x _ hx
    intro l
    by_cases hl : l=j
    · subst l
      simp [abs_of_pos hr]
    · simp [Pi.single_apply,hl,Ne.symm hl,hr.le]
  have hb := inverse_entry (Trajectory.run d k) x (Thickening.radius d) hr hR hbase j hperturb i
  have hpow : (0:ℚ)<(2^RadiusBudget.exponent d:ℕ) := by positivity
  have hinv : 1/Thickening.radius d≤((2^RadiusBudget.exponent d:ℕ):ℚ) := by
    have h := one_div_le_one_div_of_le (by positivity : (0:ℚ)<1/(2^RadiusBudget.exponent d:ℕ))
      (RadiusBudget.radius_lower d)
    simpa only [one_div_one_div] using h
  calc
    _ ≤ 2/Thickening.radius d := hb
    _ ≤ 2*((2^RadiusBudget.exponent d:ℕ):ℚ) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℚ)≤2)
    _ = _ := by simp [pow_succ]; ring

theorem actual_inverse_det (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hf : ∃ x, Codec.Feasible d x) :
    |(Trajectory.run d k).factor⁻¹.det|≤(2^exponent d:ℕ) := by
  have hm := Matrix.det_le (A := (Trajectory.run d k).factor⁻¹)
    (abv := (AbsoluteValue.abs : AbsoluteValue ℚ ℚ)) (actual_inverse_entry d hn k hf)
  have hp := DeterminantGap.bound_le_power d.dimension
    (2^(RadiusBudget.exponent d+1)) (RadiusBudget.exponent d+1) le_rfl
  have hp' : ((DeterminantGap.bound d.dimension (2^(RadiusBudget.exponent d+1)):ℕ):ℚ)≤
      ((2^exponent d:ℕ):ℚ) := by exact_mod_cast hp
  have hm' : |((Trajectory.run d k).factor⁻¹).det| ≤
      ((DeterminantGap.bound d.dimension (2^(RadiusBudget.exponent d+1)) : ℕ) : ℚ) := by
    simpa [Fintype.card_fin,nsmul_eq_mul,DeterminantGap.bound] using hm
  exact hm'.trans hp'

theorem actual_det_lower (d : Codec.Raw) (hn : 2≤d.dimension) (k : ℕ)
    (hf : ∃ x, Codec.Feasible d x) :
    1/((2^exponent d:ℕ):ℚ)≤|(Trajectory.run d k).factor.det| := by
  have hR := (Trajectory.invariant d hn k).1
  have he := Matrix.det_nonsing_inv_mul_det (Trajectory.run d k).factor
    (isUnit_iff_ne_zero.mpr hR)
  have hab : |((Trajectory.run d k).factor⁻¹).det| * |(Trajectory.run d k).factor.det| = (1 : ℚ) := by
    rw [← abs_mul,he]
    norm_num
  have hb := actual_inverse_det d hn k hf
  have hm := mul_le_mul_of_nonneg_right hb (abs_nonneg (Trajectory.run d k).factor.det)
  apply (div_le_iff₀ (by positivity : (0:ℚ)<(2^exponent d:ℕ))).mpr
  rw [hab] at hm
  simpa only [mul_comm] using hm

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.InverseBounds
