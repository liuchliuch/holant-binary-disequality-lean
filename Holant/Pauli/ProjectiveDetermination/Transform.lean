import Holant.Pauli.ProjectiveDetermination.Bell
import Holant.Pauli.ProjectiveDetermination.Ports

/-! A faithful Bell-coordinate transform on arbitrary finite physical port
sets. Inversion is proved from finite sums, preserving all tensor coefficients. -/
namespace Holant.Pauli.ProjectiveDetermination
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev PairedTensor (ι : Type*) := (ι → Local) → ℂ

def transform (W : PairedTensor ι) (l : ι → Label) : ℂ :=
  ∑ x : ι → Local, W x * ∏ i, bell (l i) (x i)

theorem coordinate_delta (x y : ι → Local) :
    ∏ i, (if x i = y i then (2 : ℂ) else 0) =
      if x = y then (2 : ℂ)^Fintype.card ι else 0 := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [if_neg h]
    have hi : ∃ i, x i ≠ y i := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    obtain ⟨i,hi⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Unnormalized Bell vectors have Gram matrix2I, so the tensor transform has
exact inverse factor2^number-of-physical-ports. -/
theorem transform_inversion (W : PairedTensor ι) (y : ι → Local) :
    (∑ l : ι → Label, transform W l * ∏ i, bell (l i) (y i)) =
      (2 : ℂ)^Fintype.card ι * W y := by
  classical
  unfold transform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ x : ι → Local, ∑ l : ι → Label, (W x * ∏ i, bell (l i) (x i)) * ∏ i, bell (l i) (y i)) =
        ∑ x : ι → Local, W x * ∏ i, ∑ j : Label, bell j (x i)*bell j (y i) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun i (j : Label) => bell j (x i)*bell j (y i))).symm
    _ = ∑ x : ι → Local, W x * (if x = y then (2 : ℂ)^Fintype.card ι else 0) := by
      simp_rw [bell_complete,coordinate_delta]
    _ = (2 : ℂ)^Fintype.card ι*W y := by simp [mul_ite,mul_comm]

theorem transform_zero (W : PairedTensor ι) (h : ∀ l, transform W l = 0) : W = 0 := by
  funext y
  have hh := transform_inversion W y
  simp only [h,zero_mul,Finset.sum_const_zero] at hh
  have hp : (2 : ℂ)^Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp hh.symm).resolve_left hp

/-- Splitting the literal physical ports is an equality of sums, not a chosen
index enumeration or an assumed Bell-support decomposition. -/
theorem transform_pair (W : PairedTensor ι) (r s : ι) (hne : r ≠ s) (l : ι → Label) :
    transform W l = ∑ a : Local, ∑ b : Local, ∑ z : Rest r s → Local,
      W (fill r s a b z) * (bell (l r) a*bell (l s) b*∏ i : Rest r s, bell (l i) (z i)) := by
  unfold transform
  rw [sum_assignments r s hne]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro z hz
  rw [prod_ports r s hne]
  simp only [fill_left,fill_right r s hne,fill_rest]

end
end Holant.Pauli.ProjectiveDetermination
