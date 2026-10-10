import Holant.Marked.WeightedGauge.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Every flattening rank and every protected two-by-two minor under port gauges. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open scoped BigOperators
variable {K P I J : Type*} [Field K] [Fintype P] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def flatten (e : I ⊕ J ≃ P) (f : Tensor K P) : Matrix (I → Bool) (J → Bool) K :=
  fun x y => f (fun p => Sum.elim x y (e.symm p))

theorem weight_split (e : I ⊕ J ≃ P) (r : P → K) (x : I → Bool) (y : J → Bool) :
    weight r (fun p => Sum.elim x y (e.symm p)) =
      weight (fun i => r (e (.inl i))) x * weight (fun j => r (e (.inr j))) y := by
  unfold weight
  rw [← e.prod_comp (fun p => bitWeight (r p) (Sum.elim x y (e.symm p)))]
  simp [Fintype.prod_sum_type]

theorem flatten_gauge_apply (e : I ⊕ J ≃ P) (r : P → K) (f : Tensor K P)
    (x : I → Bool) (y : J → Bool) :
    flatten e (gauge r f) x y = weight (fun i => r (e (.inl i))) x *
      flatten e f x y * weight (fun j => r (e (.inr j))) y := by
  rw [flatten, gauge, weight_split]
  simp only [flatten]
  ring

theorem flatten_gauge (e : I ⊕ J ≃ P) (r : P → K) (f : Tensor K P) :
    flatten e (gauge r f) = Matrix.diagonal (weight (fun i => r (e (.inl i)))) *
      flatten e f * Matrix.diagonal (weight (fun j => r (e (.inr j)))) := by
  classical
  ext x y
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, flatten_gauge_apply]

/-- All ordered partitions, including unequal block sizes, preserve their exact matrix rank. -/
theorem flatten_rank (e : I ⊕ J ≃ P) (r : P → K) (hr : ∀ p, r p ≠ 0) (f : Tensor K P) :
    (flatten e (gauge r f)).rank = (flatten e f).rank := by
  classical
  rw [flatten_gauge, Matrix.rank_mul_eq_left_of_det_ne_zero,
    Matrix.rank_mul_eq_right_of_det_ne_zero]
  · simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun x _ => weight_ne_zero _ (fun i => hr _) x)
  · simp only [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun y _ => weight_ne_zero _ (fun j => hr _) y)

def minor {A B : Type*} (M : Matrix A B K) (a a' : A) (b b' : B) : K :=
  M a b * M a' b' - M a b' * M a' b

/-- The protected determinant gets the four explicit nonzero row/column weights. -/
theorem minor_row_column {A B : Type*} (M : Matrix A B K) (r : A → K) (c : B → K)
    (a a' : A) (b b' : B) :
    minor (fun x y => r x * M x y * c y) a a' b b' =
      (r a * r a' * c b * c b') * minor M a a' b b' := by
  simp only [minor]
  ring

theorem flatten_minor (e : I ⊕ J ≃ P) (r : P → K) (f : Tensor K P)
    (x x' : I → Bool) (y y' : J → Bool) :
    minor (flatten e (gauge r f)) x x' y y' =
      (weight (fun i => r (e (.inl i))) x * weight (fun i => r (e (.inl i))) x' *
       weight (fun j => r (e (.inr j))) y * weight (fun j => r (e (.inr j))) y') *
      minor (flatten e f) x x' y y' := by
  simp only [minor, flatten_gauge_apply]
  ring

theorem minor_zero_iff {A B : Type*} (M : Matrix A B K) (r : A → K) (c : B → K)
    (hr : ∀ a, r a ≠ 0) (hc : ∀ b, c b ≠ 0) (a a' : A) (b b' : B) :
    minor (fun x y => r x * M x y * c y) a a' b b' = 0 ↔ minor M a a' b b' = 0 := by
  rw [minor_row_column]
  simp [hr, hc]

end Holant.Marked.WeightedGauge
