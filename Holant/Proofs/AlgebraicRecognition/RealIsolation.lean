import Holant.Proofs.AlgebraicRecognition.IntervalArithmetic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue


namespace Holant.LocalDrafts.EffectiveAlgebraic.RealIsolation

def derivativeCode : RationalPolynomialCode → RationalPolynomialCode
  | [] => []
  | (k, q) :: rest => (k - 1, q * k) :: derivativeCode rest

theorem derivativeCode_correct (p : RationalPolynomialCode) :
    (derivativeCode p).polynomial = p.polynomial.derivative := by
  induction p with
  | nil => simp [derivativeCode, RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    simp [derivativeCode, RationalPolynomialCode.polynomial,
      Polynomial.derivative_add, Polynomial.derivative_monomial, ih]

theorem evalRational_cast (p : RationalPolynomialCode) (q : ℚ) :
    (p.evalRational q : ℝ) = Polynomial.aeval (q : ℝ) p.polynomial := by
  induction p with
  | nil => simp [RationalPolynomialCode.evalRational, RationalPolynomialCode.polynomial]
  | cons t ts ih =>
    rcases t with ⟨k, a⟩
    simp [RationalPolynomialCode.evalRational, RationalPolynomialCode.polynomial, ih]

structure Interval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Encodable

def Interval.Contains (I : Interval) (x : ℝ) : Prop :=
  (I.lower : ℝ) ≤ x ∧ x ≤ (I.upper : ℝ)

def Interval.ball (I : Interval) : RationalBall :=
  RationalBall.ofEndpoints I.lower I.upper

def Interval.midpoint (I : Interval) : ℚ := (I.lower + I.upper) / 2
def Interval.width (I : Interval) : ℚ := I.upper - I.lower

def Brackets (p : RationalPolynomialCode) (I : Interval) : Prop :=
  I.lower ≤ I.upper ∧ p.evalRational I.lower ≤ 0 ∧ 0 ≤ p.evalRational I.upper

/-- Every decision and arithmetic operation here is on rationals. -/
def check (p : RationalPolynomialCode) (I : Interval) : Bool :=
  decide (I.lower < I.upper ∧ p.evalRational I.lower < 0 ∧
    0 < p.evalRational I.upper ∧
    0 < (RationalBall.eval I.ball (derivativeCode p)).lower)

theorem brackets_of_check {p : RationalPolynomialCode} {I : Interval}
    (h : check p I = true) : Brackets p I := by
  simp only [check, decide_eq_true_eq] at h
  exact ⟨h.1.le, h.2.1.le, h.2.2.1.le⟩

theorem brackets_exists {p : RationalPolynomialCode} {I : Interval} (h : Brackets p I) :
    ∃ x : ℝ, I.Contains x ∧ Polynomial.aeval x p.polynomial = 0 := by
  have hl : Polynomial.aeval (I.lower : ℝ) p.polynomial ≤ 0 := by
    rw [← evalRational_cast]
    exact_mod_cast h.2.1
  have hu : 0 ≤ Polynomial.aeval (I.upper : ℝ) p.polynomial := by
    rw [← evalRational_cast]
    exact_mod_cast h.2.2
  have hi : (I.lower : ℝ) ≤ I.upper := by exact_mod_cast h.1
  exact intermediate_value_Icc hi p.polynomial.continuous_aeval.continuousOn ⟨hl, hu⟩

theorem strictMono_of_check {p : RationalPolynomialCode} {I : Interval}
    (h : check p I = true) :
    StrictMonoOn (fun x : ℝ => Polynomial.aeval x p.polynomial)
      (Set.Icc (I.lower : ℝ) I.upper) := by
  simp only [check, decide_eq_true_eq] at h
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) p.polynomial.continuous_aeval.continuousOn
  intro x hx
  have hx' := interior_subset hx
  have he := RationalBall.eval_contains
    (RationalBall.contains_ofEndpoints hx'.1 hx'.2) (derivativeCode p)
  have hb := (RationalBall.contains_iff_bounds _ _).mp he
  have hp : (0 : ℝ) < (RationalBall.eval I.ball (derivativeCode p)).lower := by
    exact_mod_cast h.2.2.2
  rw [Polynomial.deriv_aeval]
  rw [derivativeCode_correct] at hb
  exact hp.trans_le hb.1

/-- The certifier proves a unique real zero, including its existence. -/
theorem check_sound {p : RationalPolynomialCode} {I : Interval} (h : check p I = true) :
    ∃! x : ℝ, I.Contains x ∧ Polynomial.aeval x p.polynomial = 0 := by
  obtain ⟨x, hx, hroot⟩ := brackets_exists (brackets_of_check h)
  refine ⟨x, ⟨hx, hroot⟩, ?_⟩
  intro y hy
  exact (strictMono_of_check h).injOn hy.1 hx (hy.2.trans hroot.symm)

/-- An exact rational root is retained as a singleton interval. -/
def bisect (p : RationalPolynomialCode) (I : Interval) : Interval :=
  let m := I.midpoint
  if p.evalRational m = 0 then ⟨m, m⟩
  else if p.evalRational m < 0 then ⟨m, I.upper⟩ else ⟨I.lower, m⟩

theorem bisect_brackets {p : RationalPolynomialCode} {I : Interval}
    (h : Brackets p I) : Brackets p (bisect p I) := by
  unfold bisect
  dsimp only
  split_ifs with hz hn
  · exact ⟨le_rfl, hz.le, hz.ge⟩
  · exact ⟨by dsimp [Interval.midpoint]; linarith [h.1], hn.le, h.2.2⟩
  · exact ⟨by dsimp [Interval.midpoint]; linarith [h.1], h.2.1, le_of_not_gt hn⟩

theorem bisect_bounds (p : RationalPolynomialCode) {I : Interval} (h : I.lower ≤ I.upper) :
    I.lower ≤ (bisect p I).lower ∧ (bisect p I).upper ≤ I.upper := by
  unfold bisect
  dsimp only
  split_ifs <;> dsimp [Interval.midpoint] <;> constructor <;> linarith

theorem bisect_width (p : RationalPolynomialCode) {I : Interval} (h : I.lower ≤ I.upper) :
    (bisect p I).width ≤ I.width / 2 := by
  unfold bisect
  dsimp only
  split_ifs <;> dsimp [Interval.width, Interval.midpoint] <;> linarith

def refine (p : RationalPolynomialCode) (I : Interval) : ℕ → Interval
  | 0 => I
  | n + 1 => bisect p (refine p I n)

theorem refine_brackets {p : RationalPolynomialCode} {I : Interval}
    (h : Brackets p I) (n : ℕ) : Brackets p (refine p I n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact bisect_brackets ih

theorem refine_bounds {p : RationalPolynomialCode} {I : Interval}
    (h : Brackets p I) (n : ℕ) :
    I.lower ≤ (refine p I n).lower ∧ (refine p I n).upper ≤ I.upper := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    have hs := bisect_bounds p (refine_brackets h n).1
    exact ⟨ih.1.trans hs.1, hs.2.trans ih.2⟩

theorem refine_width {p : RationalPolynomialCode} {I : Interval}
    (h : Brackets p I) (n : ℕ) :
    (refine p I n).width ≤ I.width / (2 : ℚ) ^ n := by
  induction n with
  | zero => simp [refine]
  | succ n ih =>
    calc
      (refine p I (n + 1)).width ≤ (refine p I n).width / 2 :=
        bisect_width p (refine_brackets h n).1
      _ ≤ (I.width / (2 : ℚ) ^ n) / 2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = I.width / (2 : ℚ) ^ (n + 1) := by rw [pow_succ, div_div]

/-- Every refinement encloses the same certified root, not an unspecified
possibly different zero at each step. -/
theorem refine_contains {p : RationalPolynomialCode} {I : Interval}
    (h : check p I = true) {x : ℝ} (hx : I.Contains x)
    (hroot : Polynomial.aeval x p.polynomial = 0) (n : ℕ) :
    (refine p I n).Contains x := by
  have hb := brackets_of_check h
  obtain ⟨y, hy, hyroot⟩ := brackets_exists (refine_brackets hb n)
  have hs := refine_bounds hb n
  have hl : (I.lower : ℝ) ≤ (refine p I n).lower := by exact_mod_cast hs.1
  have hu : ((refine p I n).upper : ℝ) ≤ I.upper := by exact_mod_cast hs.2
  have hyI : I.Contains y := ⟨hl.trans hy.1, hy.2.trans hu⟩
  have he : y = x := (strictMono_of_check h).injOn hyI hx (hyroot.trans hroot.symm)
  simpa only [he] using hy

/-- `some true` means first root < second; `some false` means second < first.
`none` is inconclusive, and is never treated as equality. -/
def separateAt (p : RationalPolynomialCode) (I : Interval)
    (q : RationalPolynomialCode) (J : Interval) (n : ℕ) : Option Bool :=
  let A := refine p I n
  let B := refine q J n
  if A.upper < B.lower then some true
  else if B.upper < A.lower then some false else none

theorem separateAt_sound {p q : RationalPolynomialCode} {I J : Interval}
    (hp : check p I = true) (hq : check q J = true)
    {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y)
    (hpx : Polynomial.aeval x p.polynomial = 0)
    (hqy : Polynomial.aeval y q.polynomial = 0) (n : ℕ) (b : Bool)
    (h : separateAt p I q J n = some b) : if b then x < y else y < x := by
  have hx' := refine_contains hp hx hpx n
  have hy' := refine_contains hq hy hqy n
  unfold separateAt at h
  dsimp only at h
  split_ifs at h with hlt hgt
  · have hb : b = true := (Option.some.inj h).symm
    subst b
    have hs : ((refine p I n).upper : ℝ) < (refine q J n).lower := by exact_mod_cast hlt
    exact hx'.2.trans_lt (hs.trans_le hy'.1)
  · have hb : b = false := (Option.some.inj h).symm
    subst b
    have hs : ((refine q J n).upper : ℝ) < (refine p I n).lower := by exact_mod_cast hgt
    exact hy'.2.trans_lt (hs.trans_le hx'.1)

/-- For any two distinct ordered certified real roots, finite bisection
eventually separates the boxes. The bound is proved from the actual geometric
width estimate, not assumed as a progress or termination condition. -/
theorem eventual_separation {p q : RationalPolynomialCode} {I J : Interval}
    (hp : check p I = true) (hq : check q J = true)
    {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y)
    (hpx : Polynomial.aeval x p.polynomial = 0)
    (hqy : Polynomial.aeval y q.polynomial = 0) (hxy : x < y) :
    ∃ n, (refine p I n).upper < (refine q J n).lower := by
  have hgap : 0 < y - x := sub_pos.mpr hxy
  obtain ⟨n, hn⟩ := exists_nat_gt (((I.width : ℝ) + (J.width : ℝ)) / (y - x))
  have hpow : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast n.lt_two_pow_self
  have htotal : (I.width : ℝ) + (J.width : ℝ) < (y - x) * (2 : ℝ) ^ n := by
    have he := (div_lt_iff₀ hgap).mp (hn.trans hpow)
    simpa only [mul_comm] using he
  have hden : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hA : ((refine p I n).width : ℝ) ≤ (I.width : ℝ) / (2 : ℝ) ^ n := by
    exact_mod_cast refine_width (brackets_of_check hp) n
  have hB : ((refine q J n).width : ℝ) ≤ (J.width : ℝ) / (2 : ℝ) ^ n := by
    exact_mod_cast refine_width (brackets_of_check hq) n
  have hsum : ((refine p I n).width : ℝ) + ((refine q J n).width : ℝ) < y - x := by
    calc
      _ ≤ (I.width : ℝ) / (2 : ℝ) ^ n + (J.width : ℝ) / (2 : ℝ) ^ n :=
        add_le_add hA hB
      _ = ((I.width : ℝ) + (J.width : ℝ)) / (2 : ℝ) ^ n := (add_div _ _ _).symm
      _ < y - x := (div_lt_iff₀ hden).mpr htotal
  have hx' := refine_contains hp hx hpx n
  have hy' := refine_contains hq hy hqy n
  have hsep : ((refine p I n).upper : ℝ) < (refine q J n).lower := by
    simp only [Interval.width, Rat.cast_sub] at hsum
    linarith [hx'.1, hy'.2]
  exact ⟨n, by exact_mod_cast hsep⟩

theorem separateAt_complete_for_distinct {p q : RationalPolynomialCode} {I J : Interval}
    (hp : check p I = true) (hq : check q J = true)
    {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y)
    (hpx : Polynomial.aeval x p.polynomial = 0)
    (hqy : Polynomial.aeval y q.polynomial = 0) (hxy : x ≠ y) :
    ∃ n, (separateAt p I q J n).isSome = true := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨n, hn⟩ := eventual_separation hp hq hx hy hpx hqy hlt
    exact ⟨n, by simp [separateAt, hn]⟩
  · obtain ⟨n, hn⟩ := eventual_separation hq hp hy hx hqy hpx hgt
    refine ⟨n, ?_⟩
    by_cases h : (refine p I n).upper < (refine q J n).lower
    · simp [separateAt, h]
    · simp [separateAt, h, hn]

end Holant.LocalDrafts.EffectiveAlgebraic.RealIsolation
