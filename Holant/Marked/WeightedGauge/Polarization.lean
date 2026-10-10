import Holant.Marked.WeightedGauge.Traces
import Holant.Dihedral.PolarizedDeterminant.Cards

/-! The complete two-copy polarization grid with both physical ports of every
closed matching edge visible. The two copies have independent internal assignments;
the literal diagonal kernels force their common lift. -/
noncomputable section
namespace Holant.Marked.WeightedGauge.Polarization
open scoped BigOperators
open Holant.Dihedral.PolarizedDeterminant

variable {s : ℕ}

def remaining (i k : Fin s) : Finset (Fin s) := Finset.univ.filter fun j => j ≠ i ∧ j ≠ k

def linkWeight (d : ℂ) (parity : Fin s → Bool) (i k : Fin s) (lam : Fin s → ℂ)
    (z y : Cube s) : ℂ := ∏ j ∈ remaining i k,
  effectiveKernel d false (lam j) (z j) (y j) *
    effectiveKernel d false 1 (z j ^^ parity j) (y j ^^ parity j)

/-- Literal two-copy matching contraction: one weighted k-link, and two
corresponding physical links at every remaining edge, only one carrying phase. -/
def physicalGrid (d : ℂ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s) (lam : Fin s → ℂ) (a b xi : Bool) : ℂ :=
  effectiveKernel d false 1 xi xi *
    ∑ z ∈ sliceWords i k, ∑ y ∈ sliceWords i k,
      linkWeight d parity i k lam z y *
        w (insert i k a xi z) * w (insert i k b xi y)

theorem diagonal_off (d t : ℂ) (a b : Bool) (h : a ≠ b) : effectiveKernel d false t a b = 0 := by
  cases a <;> cases b <;> simp_all [effectiveKernel_apply]

theorem diagonal_on (d t : ℂ) (a : Bool) : effectiveKernel d false t a a = bitWeight d a * bitWeight t a := by
  cases a <;> simp [effectiveKernel_apply]

theorem linkWeight_off (d : ℂ) (parity : Fin s → Bool) (i k : Fin s) (lam : Fin s → ℂ)
    (z y : Cube s) (hz : z ∈ sliceWords i k) (hy : y ∈ sliceWords i k) (hne : y ≠ z) :
    linkWeight d parity i k lam z y = 0 := by
  obtain ⟨j,hj⟩ : ∃ j, z j ≠ y j := by
    by_contra hn
    apply hne
    funext j
    by_contra h
    exact hn ⟨j,Ne.symm h⟩
  have hji : j ≠ i := by
    intro h; subst j
    apply hj
    exact ((mem_sliceWords i k z).mp hz).1.trans (((mem_sliceWords i k y).mp hy).1.symm)
  have hjk : j ≠ k := by
    intro h; subst j
    apply hj
    exact ((mem_sliceWords i k z).mp hz).2.trans (((mem_sliceWords i k y).mp hy).2.symm)
  unfold linkWeight
  apply Finset.prod_eq_zero (i := j) (by simp [remaining, hji, hjk])
  rw [diagonal_off d (lam j) (z j) (y j) hj, zero_mul]

/-- The matching constraints give a unique common tuple; no diagonal input relation is assumed. -/
theorem collapse (d : ℂ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s) (lam : Fin s → ℂ) (a b xi : Bool) :
    physicalGrid d parity w i k lam a b xi = bitWeight d xi *
      ∑ z ∈ sliceWords i k, linkWeight d parity i k lam z z *
        w (insert i k a xi z) * w (insert i k b xi z) := by
  rw [physicalGrid, diagonal_on]
  simp only [bitWeight_one, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_eq_single z
  · intro y hy hne
    rw [linkWeight_off d parity i k lam z y hz hy hne]
    simp
  · intro hn; exact (hn hz).elim

def constant (d : ℂ) (parity : Fin s → Bool) (i k : Fin s) : ℂ :=
  ∏ j ∈ remaining i k, if parity j then d else 1

def shiftedPhases (d : ℂ) (parity : Fin s → Bool) (i k : Fin s) (lam : Fin s → ℂ) : Fin s → ℂ :=
  fun j => if j ∈ remaining i k ∧ parity j = false then d^2 * lam j else lam j

theorem link_on (d t : ℂ) (p z : Bool) :
    effectiveKernel d false t z z * effectiveKernel d false 1 (z ^^ p) (z ^^ p) =
      (if p then d else 1) * bitWeight (if p then t else d^2*t) z := by
  cases p <;> cases z <;> simp [effectiveKernel_apply, bitWeight] <;> ring

theorem linkWeight_on (d : ℂ) (parity : Fin s → Bool) (i k : Fin s) (lam : Fin s → ℂ)
    (z : Cube s) (hz : z ∈ sliceWords i k) :
    linkWeight d parity i k lam z z = constant d parity i k * phaseMonomial (shiftedPhases d parity i k lam) z := by
  simp only [linkWeight, link_on, Finset.prod_mul_distrib, constant]
  congr 1
  rw [← Finset.prod_ite_mem_eq (remaining i k) (fun j => bitWeight (if parity j then lam j else d^2*lam j) (z j))]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hr : j ∈ remaining i k
  · cases hp : parity j <;> cases hzt : z j <;>
      simp [hr, hp, hzt, bitWeight, shiftedPhases]
  · have hzj : z j = false := by
      by_cases hji : j=i
      · subst j; exact ((mem_sliceWords i k z).mp hz).1
      · have hjk : j=k := by simpa [remaining, hji] using hr
        subst j; exact ((mem_sliceWords i k z).mp hz).2
    simp [hr, hzj]

/-- One fixed external gauge and one fixed coordinatewise phase relabeling serve the entire grid. -/
theorem physicalGrid_standard (d : ℂ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s) (lam : Fin s → ℂ) (a b xi : Bool) :
    physicalGrid d parity w i k lam a b xi =
      (bitWeight d xi * constant d parity i k) * card w i k (shiftedPhases d parity i k lam) a b xi := by
  rw [collapse]
  simp only [card, Finset.mul_sum, mul_assoc]
  apply Finset.sum_congr rfl
  intro z hz
  rw [linkWeight_on d parity i k lam z hz]
  ring

/-- The original first copy receives these fixed physical endpoint factors;
there is no phase or product choice in this parent gauge. -/
def leftGauge (d : ℂ) (parity : Fin s → Bool) (i k : Fin s) (w : Cube s → ℂ) : Cube s → ℂ :=
  fun x => bitWeight d (x k) * (∏ j ∈ remaining i k,
    bitWeight d (x j) * bitWeight d (x j ^^ parity j)) * w x

theorem phaseMonomial_remaining (i k : Fin s) (lam : Fin s → ℂ) (z : Cube s)
    (hz : z ∈ sliceWords i k) :
    phaseMonomial lam z = ∏ j ∈ remaining i k, bitWeight (lam j) (z j) := by
  rw [← Finset.prod_ite_mem_eq (remaining i k) (fun j => bitWeight (lam j) (z j))]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hr : j ∈ remaining i k
  · cases z j <;> simp [hr, bitWeight]
  · have hzj : z j = false := by
      by_cases hji : j=i
      · subst j; exact ((mem_sliceWords i k z).mp hz).1
      · have hjk : j=k := by simpa [remaining, hji] using hr
        subst j; exact ((mem_sliceWords i k z).mp hz).2
    simp [hr, hzj]

/-- Before grid reparameterization, the complete batch already uses one fixed
pair of original parent occurrences: the fixed gauged first copy and the second copy. -/
theorem physicalGrid_fixed_parent (d : ℂ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s) (hik : i ≠ k) (lam : Fin s → ℂ) (a b xi : Bool) :
    physicalGrid d parity w i k lam a b xi =
      ∑ z ∈ sliceWords i k, phaseMonomial lam z * leftGauge d parity i k w (insert i k a xi z) *
        w (insert i k b xi z) := by
  rw [collapse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  have hremain (j : Fin s) (hj : j ∈ remaining i k) : insert i k a xi z j = z j := by
    have hh := (Finset.mem_filter.mp hj).2
    simp [Holant.Dihedral.PolarizedDeterminant.insert, Function.update_apply, hh.1, hh.2]
  have hp : (∏ j ∈ remaining i k, bitWeight d (insert i k a xi z j) *
      bitWeight d (insert i k a xi z j ^^ parity j)) =
      ∏ j ∈ remaining i k, bitWeight d (z j) * bitWeight d (z j ^^ parity j) := by
    apply Finset.prod_congr rfl
    intro j hj; rw [hremain j hj]
  have hl : linkWeight d parity i k lam z z =
      phaseMonomial lam z * (∏ j ∈ remaining i k, bitWeight d (z j) * bitWeight d (z j ^^ parity j)) := by
    rw [phaseMonomial_remaining i k lam z hz, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [diagonal_on, bitWeight_one, mul_one]
    ring
  rw [hl]
  simp only [leftGauge]
  rw [hp, show insert i k a xi z k = xi by simp [Holant.Dihedral.PolarizedDeterminant.insert]]
  ring

theorem constant_ne_zero (d : ℂ) (hd : d ≠ 0) (parity : Fin s → Bool) (i k : Fin s) :
    constant d parity i k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj; cases parity j <;> simp [hd]

theorem shiftedPhases_roots {m : ℕ} (d : ℂ) (hd : (d^2)^m=1) (parity : Fin s → Bool)
    (i k : Fin s) (lam : Fin s → ℂ) (h : ∀ j, lam j ^ m = 1) :
    ∀ j, shiftedPhases d parity i k lam j ^ m = 1 := by
  intro j
  unfold shiftedPhases
  split_ifs <;> simp [mul_pow, hd, h]

theorem shiftedPhases_inverse (d : ℂ) (hd : d ≠ 0) (parity : Fin s → Bool) (i k : Fin s)
    (lam : Fin s → ℂ) : shiftedPhases d⁻¹ parity i k (shiftedPhases d parity i k lam) = lam := by
  funext j
  unfold shiftedPhases
  split_ifs <;> simp [inv_pow, hd, mul_assoc]

theorem complete_grid_surjective {m : ℕ} (d : ℂ) (hd : d ≠ 0) (hdroot : (d^2)^m=1)
    (parity : Fin s → Bool) (i k : Fin s) (lam : Fin s → ℂ) (h : ∀ j, lam j^m=1) :
    ∃ mu : Fin s → ℂ, (∀ j, mu j^m=1) ∧ shiftedPhases d parity i k mu = lam := by
  refine ⟨shiftedPhases d⁻¹ parity i k lam, ?_, ?_⟩
  · apply shiftedPhases_roots _ _ _ _ _ _ h
    simp [inv_pow, hdroot]
  · simpa only [inv_inv] using shiftedPhases_inverse d⁻¹ (inv_ne_zero hd) parity i k lam

/-- The source cross-slice Gamma receives the explicit nonzero gauge factor d*C². -/
theorem gamma_multiplier (d : ℂ) (parity : Fin s → Bool) (w : Cube s → ℂ)
    (i k : Fin s) (lam : Fin s → ℂ) :
    physicalGrid d parity w i k lam false false false * physicalGrid d parity w i k lam true false true -
      physicalGrid d parity w i k lam false false true * physicalGrid d parity w i k lam true false false =
    (d * constant d parity i k ^ 2) *
      (card w i k (shiftedPhases d parity i k lam) false false false *
        card w i k (shiftedPhases d parity i k lam) true false true -
       card w i k (shiftedPhases d parity i k lam) false false true *
        card w i k (shiftedPhases d parity i k lam) true false false) := by
  simp only [physicalGrid_standard, bitWeight_false, bitWeight_true]
  ring

end Holant.Marked.WeightedGauge.Polarization
