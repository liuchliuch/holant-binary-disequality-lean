import Holant.Proofs.AlgebraicRecognition.IntervalArithmetic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Positivity


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.BoxLimit
open Holant.LocalDrafts.EffectiveAlgebraic Filter
open scoped Topology

def BallLimit {α : Type*} (l : Filter α) (b : α → RationalBall) (x : ℝ) : Prop :=
  Tendsto (fun a => (b a).center : α → ℝ) l (𝓝 x) ∧
    Tendsto (fun a => (b a).radius : α → ℝ) l (𝓝 0)

def BoxLimit {α : Type*} (l : Filter α) (b : α → RationalBox) (z : ℂ) : Prop :=
  BallLimit l (fun a => (b a).re) z.re ∧ BallLimit l (fun a => (b a).im) z.im

section Operations
variable {α : Type*} {l : Filter α}

theorem ball_point (q : ℚ) : BallLimit l (fun _ : α => RationalBall.point q) q := by
  constructor
  · simpa only [RationalBall.point] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (q : ℝ)) l (𝓝 (q : ℝ)))
  · simpa only [RationalBall.point, Rat.cast_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0 : ℝ)) l (𝓝 (0 : ℝ)))

theorem ball_add {a b : α → RationalBall} {x y : ℝ}
    (ha : BallLimit l a x) (hb : BallLimit l b y) :
    BallLimit l (fun i => (a i).add (b i)) (x + y) := by
  constructor
  · simpa [RationalBall.add] using ha.1.add hb.1
  · simpa [RationalBall.add] using ha.2.add hb.2

theorem ball_neg {a : α → RationalBall} {x : ℝ} (ha : BallLimit l a x) :
    BallLimit l (fun i => (a i).neg) (-x) := by
  exact ⟨by simpa [RationalBall.neg] using ha.1.neg, ha.2⟩

theorem ball_mul {a b : α → RationalBall} {x y : ℝ}
    (ha : BallLimit l a x) (hb : BallLimit l b y) :
    BallLimit l (fun i => (a i).mul (b i)) (x * y) := by
  constructor
  · simpa [RationalBall.mul] using ha.1.mul hb.1
  · simpa [RationalBall.mul] using
      ((ha.2.mul hb.2).add (ha.1.abs.mul hb.2)).add (hb.1.abs.mul ha.2)

theorem box_point (q : ℚ) : BoxLimit l (fun _ : α => RationalBox.point q) (q : ℂ) := by
  constructor
  · simpa [RationalBox.point] using (ball_point (l := l) q)
  · simpa [RationalBox.point] using (ball_point (l := l) 0)

theorem box_add {a b : α → RationalBox} {z w : ℂ}
    (ha : BoxLimit l a z) (hb : BoxLimit l b w) :
    BoxLimit l (fun i => (a i).add (b i)) (z + w) :=
  ⟨ball_add ha.1 hb.1, ball_add ha.2 hb.2⟩

theorem box_mul {a b : α → RationalBox} {z w : ℂ}
    (ha : BoxLimit l a z) (hb : BoxLimit l b w) :
    BoxLimit l (fun i => (a i).mul (b i)) (z * w) := by
  constructor
  · simpa only [RationalBox.mul, Complex.mul_re, sub_eq_add_neg] using
      ball_add (ball_mul ha.1 hb.1) (ball_neg (ball_mul ha.2 hb.2))
  · exact ball_add (ball_mul ha.1 hb.2) (ball_mul ha.2 hb.1)

theorem box_power {b : α → RationalBox} {z : ℂ} (hb : BoxLimit l b z) (n : ℕ) :
    BoxLimit l (fun i => (b i).power n) (z ^ n) := by
  induction n with
  | zero => simpa [RationalBox.power] using (box_point (l := l) 1)
  | succ n ih => simpa only [RationalBox.power, pow_succ] using box_mul ih hb

theorem box_eval {b : α → RationalBox} {z : ℂ} (hb : BoxLimit l b z)
    (e : RationalPolynomialCode) :
    BoxLimit l (fun i => (b i).eval e) (Polynomial.aeval z e.polynomial) := by
  induction e with
  | nil => simpa [RationalBox.eval, RationalPolynomialCode.polynomial] using (box_point (l := l) 0)
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    simpa [RationalBox.eval, RationalPolynomialCode.polynomial] using
      box_add (box_mul (box_point q) (box_power hb k)) ih

theorem eventual_inside {b : α → RationalBox} {z : ℂ} (hb : BoxLimit l b z)
    (r : RationalRectangle) (hr : r.Contains z) : ∀ᶠ i in l, (b i).inside r = true := by
  have hrl : Tendsto (fun i => ((b i).re.lower : ℝ)) l (𝓝 z.re) := by
    simpa [RationalBall.lower] using hb.1.1.sub hb.1.2
  have hru : Tendsto (fun i => ((b i).re.upper : ℝ)) l (𝓝 z.re) := by
    simpa [RationalBall.upper] using hb.1.1.add hb.1.2
  have hil : Tendsto (fun i => ((b i).im.lower : ℝ)) l (𝓝 z.im) := by
    simpa [RationalBall.lower] using hb.2.1.sub hb.2.2
  have hiu : Tendsto (fun i => ((b i).im.upper : ℝ)) l (𝓝 z.im) := by
    simpa [RationalBall.upper] using hb.2.1.add hb.2.2
  filter_upwards [(tendsto_order.mp hrl).1 _ hr.1, (tendsto_order.mp hru).2 _ hr.2.1,
    (tendsto_order.mp hil).1 _ hr.2.2.1, (tendsto_order.mp hiu).2 _ hr.2.2.2]
    with i h₁ h₂ h₃ h₄
  simp only [RationalBox.inside, decide_eq_true_eq]
  exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂, by exact_mod_cast h₃, by exact_mod_cast h₄⟩

theorem eventual_family {m : ℕ} {b : α → RationalBox} {z : ℂ} (hb : BoxLimit l b z)
    (e : Fin m → RationalPolynomialCode) (r : Fin m → RationalRectangle)
    (hr : ∀ j, (r j).Contains (Polynomial.aeval z (e j).polynomial)) :
    ∀ᶠ i in l, ∀ j, ((b i).eval (e j)).inside (r j) = true :=
  Filter.eventually_all.mpr (fun j => eventual_inside (box_eval hb (e j)) (r j) (hr j))

end Operations

/-- A concrete four-coordinate smallness condition suitable for the independent
primitive-root certificate producer. It imposes no checker-success premise. -/
def Small (z : ℂ) (ε : ℝ) (b : RationalBox) : Prop :=
  |(b.re.center : ℝ) - z.re| < ε ∧ |(b.re.radius : ℝ)| < ε ∧
    |(b.im.center : ℝ) - z.im| < ε ∧ |(b.im.radius : ℝ)| < ε

theorem small_sequence_limit {z : ℂ} {b : ℕ → RationalBox}
    (h : ∀ n : ℕ, Small z (1 / ((n : ℝ) + 1)) (b n)) : BoxLimit atTop b z := by
  have conv {f : ℕ → ℝ} {x : ℝ}
      (hf : ∀ n : ℕ, |f n - x| < 1 / ((n : ℝ) + 1)) : Tendsto f atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq] using
      squeeze_zero (fun n : ℕ => abs_nonneg (f n - x)) (fun n : ℕ => (hf n).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
  exact ⟨⟨conv (f := fun n : ℕ => ((b n).re.center : ℝ)) (fun n => (h n).1),
      conv (f := fun n : ℕ => ((b n).re.radius : ℝ)) (x := 0)
        (fun n => by simpa using (h n).2.1)⟩,
    ⟨conv (f := fun n : ℕ => ((b n).im.center : ℝ)) (fun n => (h n).2.2.1),
      conv (f := fun n : ℕ => ((b n).im.radius : ℝ)) (x := 0)
        (fun n => by simpa using (h n).2.2.2)⟩⟩

/-- Every sufficiently small box works, not merely a specially chosen sequence.
This allows arbitrary certified shrinking boxes from ComplexIsolation. -/
theorem family_small {m : ℕ} (z : ℂ) (e : Fin m → RationalPolynomialCode)
    (r : Fin m → RationalRectangle)
    (hr : ∀ j, (r j).Contains (Polynomial.aeval z (e j).polynomial)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : RationalBox, Small z ε b →
      ∀ j, (b.eval (e j)).inside (r j) = true := by
  classical
  by_contra h
  push_neg at h
  have bad (n : ℕ) : ∃ b : RationalBox, Small z (1 / ((n : ℝ) + 1)) b ∧
      ¬ ∀ j, (b.eval (e j)).inside (r j) = true := by
    obtain ⟨b, hb, j, hj⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨b, hb, fun hall => hj (hall j)⟩
  choose b hb hbad using bad
  have hbLimit : BoxLimit atTop b z := small_sequence_limit hb
  have he : ∀ᶠ n : ℕ in atTop, ∀ j, ((b n).eval (e j)).inside (r j) = true :=
    eventual_family hbLimit e r hr
  obtain ⟨n, hn⟩ := he.exists
  exact hbad n hn

/-- Rational enclosing boxes can be chosen inside every smallness tolerance.
This is an existence proof, not runtime choice of a root. -/
theorem exists_small_box (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : RationalBox, b.Contains z ∧ Small z ε b := by
  obtain ⟨r, hr, hrε⟩ := exists_rat_btwn hε
  have hr' : (0 : ℝ) < r := by simpa using hr
  have center (x : ℝ) : ∃ q : ℚ, |(q : ℝ) - x| < (r : ℝ) := by
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x - r < x + r by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  obtain ⟨a, ha⟩ := center z.re
  obtain ⟨b, hb⟩ := center z.im
  refine ⟨⟨⟨a, r⟩, ⟨b, r⟩⟩, ?_, ?_⟩
  · exact ⟨by simpa [RationalBall.Contains, abs_sub_comm] using ha.le,
      by simpa [RationalBall.Contains, abs_sub_comm] using hb.le⟩
  · exact ⟨ha.trans hrε, by simpa [abs_of_pos hr'] using hrε,
      hb.trans hrε, by simpa [abs_of_pos hr'] using hrε⟩

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.BoxLimit
