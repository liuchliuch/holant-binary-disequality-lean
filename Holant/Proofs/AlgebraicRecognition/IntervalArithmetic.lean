import Holant.Proofs.AlgebraicRecognition.RootCode
import Mathlib.Algebra.Order.Group.Abs


namespace Holant.LocalDrafts.EffectiveAlgebraic

structure RationalBall where
  center : ℚ
  radius : ℚ
  deriving DecidableEq, Encodable

namespace RationalBall

def Contains (b : RationalBall) (x : ℝ) : Prop :=
  |x - (b.center : ℝ)| ≤ (b.radius : ℝ)

def lower (b : RationalBall) : ℚ := b.center - b.radius
def upper (b : RationalBall) : ℚ := b.center + b.radius
def point (q : ℚ) : RationalBall := ⟨q, 0⟩
def add (a b : RationalBall) : RationalBall :=
  ⟨a.center + b.center, a.radius + b.radius⟩
def neg (a : RationalBall) : RationalBall := ⟨-a.center, a.radius⟩
def mul (a b : RationalBall) : RationalBall :=
  ⟨a.center * b.center,
    a.radius * b.radius + |a.center| * b.radius + |b.center| * a.radius⟩

def power (a : RationalBall) : ℕ → RationalBall
  | 0 => point 1
  | n + 1 => mul (power a n) a

def ofEndpoints (l u : ℚ) : RationalBall := ⟨(l + u) / 2, (u - l) / 2⟩

theorem contains_iff_bounds (b : RationalBall) (x : ℝ) :
    b.Contains x ↔ (b.lower : ℝ) ≤ x ∧ x ≤ (b.upper : ℝ) := by
  simp only [Contains, lower, upper, Rat.cast_sub, Rat.cast_add, abs_le]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem contains_ofEndpoints {l u : ℚ} {x : ℝ}
    (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (ofEndpoints l u).Contains x := by
  rw [contains_iff_bounds]
  simp only [ofEndpoints, lower, upper, Rat.cast_sub, Rat.cast_add,
    Rat.cast_div, Rat.cast_ofNat]
  constructor <;> linarith

@[simp] theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := by
  simp [Contains, point]

theorem contains_add {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x + y) := by
  change |x + y - ((a.center + b.center : ℚ) : ℝ)| ≤
    ((a.radius + b.radius : ℚ) : ℝ)
  push_cast
  calc
    |x + y - ((a.center : ℝ) + b.center)| =
        |(x - a.center) + (y - b.center)| := by congr 1 <;> ring
    _ ≤ |x - a.center| + |y - b.center| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + b.radius := add_le_add hx hy

theorem contains_neg {a : RationalBall} {x : ℝ} (hx : a.Contains x) :
    a.neg.Contains (-x) := by
  change |-x - ((-a.center : ℚ) : ℝ)| ≤ (a.radius : ℝ)
  rw [Rat.cast_neg, neg_sub_neg, ← neg_sub x (a.center : ℝ), abs_neg]
  exact hx

theorem contains_mul {a b : RationalBall} {x y : ℝ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x * y) := by
  have ha : (0 : ℝ) ≤ a.radius := (abs_nonneg _).trans hx
  have hb : (0 : ℝ) ≤ b.radius := (abs_nonneg _).trans hy
  change |x * y - ((a.center * b.center : ℚ) : ℝ)| ≤
    ((a.radius * b.radius + |a.center| * b.radius + |b.center| * a.radius : ℚ) : ℝ)
  push_cast
  calc
    |x * y - (a.center : ℝ) * b.center| =
        |(x - a.center) * (y - b.center) +
          (a.center : ℝ) * (y - b.center) + (b.center : ℝ) * (x - a.center)| := by
      congr 1 <;> ring
    _ ≤ |(x - a.center) * (y - b.center)| +
        |(a.center : ℝ) * (y - b.center)| + |(b.center : ℝ) * (x - a.center)| :=
      (abs_add_le _ _).trans
        (add_le_add
          (abs_add_le ((x - a.center) * (y - b.center))
            ((a.center : ℝ) * (y - b.center)))
          (le_rfl : |(b.center : ℝ) * (x - a.center)| ≤
            |(b.center : ℝ) * (x - a.center)|))
    _ ≤ (a.radius : ℝ) * b.radius + |(a.center : ℝ)| * b.radius +
        |(b.center : ℝ)| * a.radius := by
      simp only [abs_mul]
      exact add_le_add
        (add_le_add (mul_le_mul hx hy (abs_nonneg _) ha)
          (mul_le_mul_of_nonneg_left hy (abs_nonneg _)))
        (mul_le_mul_of_nonneg_left hx (abs_nonneg _))

theorem contains_power {a : RationalBall} {x : ℝ} (hx : a.Contains x) (n : ℕ) :
    (a.power n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [power] using contains_point 1
  | succ n ih => simpa [power, pow_succ] using contains_mul ih hx

def eval (b : RationalBall) : RationalPolynomialCode → RationalBall
  | [] => point 0
  | (k, q) :: rest => ((point q).mul (b.power k)).add (eval b rest)

theorem eval_contains {b : RationalBall} {x : ℝ} (hx : b.Contains x)
    (p : RationalPolynomialCode) :
    (eval b p).Contains (Polynomial.aeval x p.polynomial) := by
  induction p with
  | nil => simpa [eval, RationalPolynomialCode.polynomial] using contains_point 0
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    simpa [eval, RationalPolynomialCode.polynomial] using
      contains_add (contains_mul (contains_point q) (contains_power hx k)) ih

end RationalBall

structure RationalBox where
  re : RationalBall
  im : RationalBall
  deriving DecidableEq, Encodable

namespace RationalBox

def Contains (b : RationalBox) (z : ℂ) : Prop := b.re.Contains z.re ∧ b.im.Contains z.im
def point (q : ℚ) : RationalBox := ⟨RationalBall.point q, RationalBall.point 0⟩
def add (a b : RationalBox) : RationalBox := ⟨a.re.add b.re, a.im.add b.im⟩
def neg (a : RationalBox) : RationalBox := ⟨a.re.neg, a.im.neg⟩
def mul (a b : RationalBox) : RationalBox :=
  ⟨(a.re.mul b.re).add (a.im.mul b.im).neg,
    (a.re.mul b.im).add (a.im.mul b.re)⟩
def power (a : RationalBox) : ℕ → RationalBox
  | 0 => point 1
  | n + 1 => (power a n).mul a

def ofRectangle (r : RationalRectangle) : RationalBox :=
  ⟨RationalBall.ofEndpoints r.reLower r.reUpper,
    RationalBall.ofEndpoints r.imLower r.imUpper⟩

theorem contains_ofRectangle {r : RationalRectangle} {z : ℂ} (h : r.Contains z) :
    (ofRectangle r).Contains z :=
  ⟨RationalBall.contains_ofEndpoints h.1.le h.2.1.le,
    RationalBall.contains_ofEndpoints h.2.2.1.le h.2.2.2.le⟩

@[simp] theorem contains_point (q : ℚ) : (point q).Contains (q : ℂ) := by
  constructor <;> simp [point, RationalBall.Contains, RationalBall.point]

theorem contains_add {a b : RationalBox} {x y : ℂ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.add b).Contains (x + y) :=
  ⟨RationalBall.contains_add hx.1 hy.1, RationalBall.contains_add hx.2 hy.2⟩

theorem contains_neg {a : RationalBox} {x : ℂ} (hx : a.Contains x) :
    a.neg.Contains (-x) :=
  ⟨RationalBall.contains_neg hx.1, RationalBall.contains_neg hx.2⟩

theorem contains_mul {a b : RationalBox} {x y : ℂ}
    (hx : a.Contains x) (hy : b.Contains y) : (a.mul b).Contains (x * y) := by
  constructor
  · change ((a.re.mul b.re).add (a.im.mul b.im).neg).Contains
      (x.re * y.re - x.im * y.im)
    simpa only [sub_eq_add_neg] using
      RationalBall.contains_add (RationalBall.contains_mul hx.1 hy.1)
        (RationalBall.contains_neg (RationalBall.contains_mul hx.2 hy.2))
  · exact RationalBall.contains_add (RationalBall.contains_mul hx.1 hy.2)
      (RationalBall.contains_mul hx.2 hy.1)

theorem contains_power {a : RationalBox} {x : ℂ} (hx : a.Contains x) (n : ℕ) :
    (a.power n).Contains (x ^ n) := by
  induction n with
  | zero => simpa [power] using contains_point 1
  | succ n ih => simpa [power, pow_succ] using contains_mul ih hx

def eval (b : RationalBox) : RationalPolynomialCode → RationalBox
  | [] => point 0
  | (k, q) :: rest => ((point q).mul (b.power k)).add (eval b rest)

theorem eval_contains {b : RationalBox} {x : ℂ} (hx : b.Contains x)
    (p : RationalPolynomialCode) :
    (eval b p).Contains (Polynomial.aeval x p.polynomial) := by
  induction p with
  | nil => simpa [eval, RationalPolynomialCode.polynomial] using contains_point 0
  | cons t ts ih =>
    rcases t with ⟨k, q⟩
    simpa [eval, RationalPolynomialCode.polynomial] using
      contains_add (contains_mul (contains_point q) (contains_power hx k)) ih

/-- A finite rational check proving the whole computed enclosure is strictly
inside the target's open isolating rectangle. -/
def inside (b : RationalBox) (r : RationalRectangle) : Bool :=
  decide (r.reLower < b.re.lower ∧ b.re.upper < r.reUpper ∧
    r.imLower < b.im.lower ∧ b.im.upper < r.imUpper)

theorem inside_sound {b : RationalBox} {r : RationalRectangle}
    (h : b.inside r = true) {z : ℂ} (hz : b.Contains z) : r.Contains z := by
  simp only [inside, decide_eq_true_eq] at h
  obtain ⟨hlr, hur⟩ := (RationalBall.contains_iff_bounds _ _).mp hz.1
  obtain ⟨hli, hui⟩ := (RationalBall.contains_iff_bounds _ _).mp hz.2
  have h₁ : (r.reLower : ℝ) < b.re.lower := by exact_mod_cast h.1
  have h₂ : (b.re.upper : ℝ) < r.reUpper := by exact_mod_cast h.2.1
  have h₃ : (r.imLower : ℝ) < b.im.lower := by exact_mod_cast h.2.2.1
  have h₄ : (b.im.upper : ℝ) < r.imUpper := by exact_mod_cast h.2.2.2
  exact ⟨h₁.trans_le hlr, hur.trans_lt h₂, h₃.trans_le hli, hui.trans_lt h₄⟩

end RationalBox
end Holant.LocalDrafts.EffectiveAlgebraic
