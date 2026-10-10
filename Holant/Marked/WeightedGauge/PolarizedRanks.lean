import Holant.Marked.WeightedGauge.Polarization
import Holant.Dihedral.PolarizedDeterminant.Integration

/-! All three actual polarization flattenings, zero cards included, transport
through the proved external gauge and the complete finite phase-grid relabeling. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Holant.Marked.WeightedGauge.Polarization
open Holant.Dihedral.PolarizedDeterminant
open scoped BigOperators

private theorem row_column_rank {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (M : Matrix I J ℂ) (r : I → ℂ) (c : J → ℂ)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ j, c j ≠ 0) :
    Matrix.rank (fun i j => r i * M i j * c j) = M.rank := by
  have he : (fun i j => r i * M i j * c j) = Matrix.diagonal r * M * Matrix.diagonal c := by
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [he, Matrix.rank_mul_eq_left_of_det_ne_zero, Matrix.rank_mul_eq_right_of_det_ne_zero]
  · simpa [Matrix.det_diagonal] using Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)
  · simpa [Matrix.det_diagonal] using Finset.prod_ne_zero_iff.mpr (fun j _ => hc j)

theorem threeRanks_weight_iff (q : Bool → Bool → Bool → ℂ) (c d : ℂ)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    ThreeRanks (fun a b xi => c * bitWeight d xi * q a b xi) ↔ ThreeRanks q := by
  have hfirst : Matrix.rank (fun a : Bool => fun t : Bool × Bool => c*bitWeight d t.2*q a t.1 t.2) =
      Matrix.rank (fun a : Bool => fun t : Bool × Bool => q a t.1 t.2) := by
    have he : (fun a : Bool => fun t : Bool × Bool => c*bitWeight d t.2*q a t.1 t.2) =
        (fun a : Bool => fun t : Bool × Bool => c*q a t.1 t.2*bitWeight d t.2) := by funext a t; ring
    rw [he]
    exact row_column_rank (fun a : Bool => fun t : Bool × Bool => q a t.1 t.2)
      (fun _ => c) (fun t => bitWeight d t.2) (fun _ => hc) (fun t => bitWeight_ne_zero hd t.2)
  have hsecond : Matrix.rank (fun b : Bool => fun t : Bool × Bool => c*bitWeight d t.2*q t.1 b t.2) =
      Matrix.rank (fun b : Bool => fun t : Bool × Bool => q t.1 b t.2) := by
    have he : (fun b : Bool => fun t : Bool × Bool => c*bitWeight d t.2*q t.1 b t.2) =
        (fun b : Bool => fun t : Bool × Bool => c*q t.1 b t.2*bitWeight d t.2) := by funext b t; ring
    rw [he]
    exact row_column_rank (fun b : Bool => fun t : Bool × Bool => q t.1 b t.2)
      (fun _ => c) (fun t => bitWeight d t.2) (fun _ => hc) (fun t => bitWeight_ne_zero hd t.2)
  have hthird : Matrix.rank (fun xi : Bool => fun t : Bool × Bool => c*bitWeight d xi*q t.1 t.2 xi) =
      Matrix.rank (fun xi : Bool => fun t : Bool × Bool => q t.1 t.2 xi) := by
    simpa only [mul_one] using row_column_rank (fun xi : Bool => fun t : Bool × Bool => q t.1 t.2 xi)
      (fun xi => c*bitWeight d xi) (fun _ => 1)
      (fun xi => mul_ne_zero hc (bitWeight_ne_zero hd xi)) (fun _ => one_ne_zero)
  constructor
  · intro h; exact ⟨hfirst ▸ h.first,hsecond ▸ h.second,hthird ▸ h.third⟩
  · intro h; exact ⟨hfirst.symm ▸ h.first,hsecond.symm ▸ h.second,hthird.symm ▸ h.third⟩

theorem physicalGrid_ranks_iff {s : ℕ} (d : ℂ) (hd : d ≠ 0) (parity : Fin s → Bool)
    (w : Cube s → ℂ) (i k : Fin s) (lam : Fin s → ℂ) :
    ThreeRanks (physicalGrid d parity w i k lam) ↔
      ThreeRanks (card w i k (shiftedPhases d parity i k lam)) := by
  have he : physicalGrid d parity w i k lam = fun a b xi =>
      constant d parity i k * bitWeight d xi * card w i k (shiftedPhases d parity i k lam) a b xi := by
    funext a b xi; rw [physicalGrid_standard]; ring
  rw [he]
  exact threeRanks_weight_iff _ _ _ (constant_ne_zero d hd parity i k) hd

/-- The complete grid retains all three flattenings, including every zero-card pattern. -/
theorem full_grid_ranks_iff {s m : ℕ} (d : ℂ) (hd : d ≠ 0) (hdroot : (d^2)^m=1)
    (parity : Fin s → Bool) (w : Cube s → ℂ) (i k : Fin s) :
    (∀ lam : Fin s → ℂ, (∀ j, lam j^m=1) → ThreeRanks (physicalGrid d parity w i k lam)) ↔
    (∀ lam : Fin s → ℂ, (∀ j, lam j^m=1) → ThreeRanks (card w i k lam)) := by
  constructor
  · intro h lam hlam
    obtain ⟨mu,hmu,he⟩ := complete_grid_surjective d hd hdroot parity i k lam hlam
    have hh := (physicalGrid_ranks_iff d hd parity w i k mu).mp (h mu hmu)
    simpa only [he] using hh
  · intro h lam hlam
    apply (physicalGrid_ranks_iff d hd parity w i k lam).mpr
    exact h _ (shiftedPhases_roots d hdroot parity i k lam hlam)

/-- The literal weighted physical grid feeds frozen Lemma 6.22 without assuming
coefficient ratios or any product formula for the original matching table. -/
theorem weighted_coefficient_product {s m : ℕ} (hm : 3 ≤ m) (d : ℂ) (hd : d ≠ 0)
    (hdroot : (d^2)^m=1) (parity : Fin s → Bool) (w : Cube s → ℂ) (hw : ∀ z, w z ≠ 0)
    (h : ∀ i k, i ≠ k → ∀ lam : Fin s → ℂ, (∀ j, lam j^m=1) →
      ThreeRanks (physicalGrid d parity w i k lam)) :
    (∀ i, baseRatio w i ≠ 0) ∧ ∀ x,
      w x = w (fun _ => false) * ∏ i, baseRatio w i ^ (if x i then 1 else 0 : ℕ) := by
  apply polarized_coefficient_product hm (fun _ => 1) w hw
  intro i k hik z
  apply (full_grid_ranks_iff d hd hdroot parity w i k).mp (h i k hik)
  intro j
  have hh := (z j).property
  rw [mem_rootsOfUnity] at hh
  simpa using congrArg Units.val hh

end Holant.Marked.WeightedGauge.Polarization
