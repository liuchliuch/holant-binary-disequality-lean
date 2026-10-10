import Holant.Marked.SupportAtlas.Source
import Holant.TensorClosure

/-! Portwise product weights, their exact inverse, and the endpoint-push identities. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open scoped BigOperators
variable {K : Type*} [Field K]

def bitWeight (d : K) (b : Bool) : K := if b then d else 1
@[simp] theorem bitWeight_false (d : K) : bitWeight d false = 1 := rfl
@[simp] theorem bitWeight_true (d : K) : bitWeight d true = d := rfl
@[simp] theorem bitWeight_one (b : Bool) : bitWeight (1 : K) b = 1 := by cases b <;> rfl

theorem bitWeight_ne_zero {d : K} (hd : d ≠ 0) (b : Bool) : bitWeight d b ≠ 0 := by
  cases b <;> simp [hd]

def diagonal (d : K) : Kernel K := fun a b => if a = b then bitWeight d a else 0

theorem diagonal_mul (d : K) (M : Kernel K) (a b : Bool) :
    Kernel.mul (diagonal d) M a b = bitWeight d a * M a b := by
  cases a <;> simp [Kernel.mul_apply, diagonal]

theorem mul_diagonal (d : K) (M : Kernel K) (a b : Bool) :
    Kernel.mul M (diagonal d) a b = M a b * bitWeight d b := by
  cases b <;> simp [Kernel.mul_apply, diagonal]

/-- Ordered bilinear Frobenius pairing, without conjugation. -/
def pairing (M g : Kernel K) : K := ∑ a : Bool, ∑ b : Bool, M a b * g a b

theorem push_first (d : K) (M g : Kernel K) :
    pairing (Kernel.mul (diagonal d) M) g = pairing M (fun a b => bitWeight d a * g a b) := by
  simp only [pairing, diagonal_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem push_second (d : K) (M g : Kernel K) :
    pairing (Kernel.mul M (diagonal d)) g = pairing M (fun a b => bitWeight d b * g a b) := by
  simp only [pairing, mul_diagonal]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {I : Type*} [Fintype I]

def weight (r : I → K) (x : I → Bool) : K := ∏ i, bitWeight (r i) (x i)
def gauge (r : I → K) (f : Tensor K I) : Tensor K I := fun x => weight r x * f x

theorem weight_ne_zero (r : I → K) (hr : ∀ i, r i ≠ 0) (x : I → Bool) : weight r x ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => bitWeight_ne_zero (hr i) (x i))

@[simp] theorem weight_one (x : I → Bool) : weight (fun _ => (1 : K)) x = 1 := by simp [weight]

theorem weight_mul (r s : I → K) (x : I → Bool) :
    weight (fun i => r i * s i) x = weight r x * weight s x := by
  unfold weight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi; cases x i <;> simp [bitWeight]

theorem gauge_comp (r s : I → K) (f : Tensor K I) :
    gauge r (gauge s f) = gauge (fun i => r i * s i) f := by
  funext x; simp [gauge, weight_mul, mul_assoc]

theorem gauge_comm (r s : I → K) (f : Tensor K I) : gauge r (gauge s f) = gauge s (gauge r f) := by
  simp only [gauge_comp, mul_comm]

theorem gauge_inverse (r : I → K) (hr : ∀ i, r i ≠ 0) (f : Tensor K I) :
    gauge (fun i => (r i)⁻¹) (gauge r f) = f := by
  rw [gauge_comp]
  funext x
  simp [hr, gauge]

theorem gauge_zero_iff (r : I → K) (hr : ∀ i, r i ≠ 0) (f : Tensor K I) (x : I → Bool) :
    gauge r f x = 0 ↔ f x = 0 := by
  simp [gauge, weight_ne_zero r hr x]

theorem gauge_eq_zero_iff (r : I → K) (hr : ∀ i, r i ≠ 0) (f : Tensor K I) :
    gauge r f = 0 ↔ f = 0 := by
  simp only [funext_iff, Pi.zero_apply, gauge_zero_iff r hr]

/-- Exact projective agreement is invariant under one common invertible port gauge. -/
theorem gauge_projective_iff (r : I → K) (hr : ∀ i, r i ≠ 0)
    (f g : Tensor K I) (c : K) : gauge r f = c • gauge r g ↔ f = c • g := by
  constructor
  · intro h; funext x
    have hx := congrFun h x
    change weight r x * f x = c * (weight r x * g x) at hx
    apply mul_left_cancel₀ (weight_ne_zero r hr x)
    change weight r x * f x = weight r x * (c * g x)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx
  · intro h; rw [h]; funext x; simp [gauge]; ring

/-- A literal set of selected original ports gives the manuscript's D_delta^(S). -/
def setWeights [DecidableEq I] (d : K) (S : Finset I) : I → K := fun i => if i ∈ S then d else 1

theorem setWeights_ne_zero [DecidableEq I] {d : K} (hd : d ≠ 0) (S : Finset I) :
    ∀ i, setWeights d S i ≠ 0 := by
  intro i; by_cases hi : i ∈ S <;> simp [setWeights, hi, hd]

theorem weight_set [DecidableEq I] (d : K) (S : Finset I) (x : I → Bool) :
    weight (setWeights d S) x = d ^ (∑ i ∈ S, if x i then 1 else 0 : ℕ) := by
  simp only [weight, setWeights]
  calc
    _ = ∏ i ∈ S, d ^ (if x i then 1 else 0 : ℕ) := by
      rw [← Finset.prod_ite_mem_eq S (fun i => d ^ (if x i then 1 else 0 : ℕ))]
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hs : i ∈ S <;> cases x i <;> simp [hs, bitWeight]
    _ = _ := Finset.prod_pow_eq_pow_sum S _ d

end Holant.Marked.WeightedGauge
