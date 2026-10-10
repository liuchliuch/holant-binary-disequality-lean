import Holant.EightVertex.LocalAffineCollapse.Phase.Basic

/-! Complement symmetry turns the local-affine tests into even, mutually
orthogonal support words, without any externally supplied support hypotheses. -/
namespace Holant.EightVertex.LocalAffineCollapse.Phase
open Holant.Tractable Holant.Tractable.AffinePhase
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (N : Signature AlgebraicComplex 4) (rho : AlgebraicComplex)
variable (hr0 : rho ≠ 0) (hr : rho ^ 8 = 1)
variable (hc : ∀ s, rho ^ Holant.weight (complementWord s) * N (complementWord s) =
  rho ^ Holant.weight s * N s)

include rho hr0 hc in
theorem support_complement (s : W) (hs : N s ≠ 0) : N (complementWord s) ≠ 0 := by
  intro hz
  have he := hc s
  rw [hz, mul_zero] at he
  exact mul_ne_zero (pow_ne_zero _ hr0) hs he.symm

include rho hr0 hr hc in
theorem complement_power (s : W) (k : ℕ)
    (hw : (k * Holant.weight (complementWord s)) % 8 = (k * Holant.weight s) % 8) :
    N (complementWord s) ^ k = N s ^ k := by
  have he := congrArg (fun a : AlgebraicComplex => a ^ k) (hc s)
  simp only [mul_pow, ← pow_mul] at he
  have hp : rho ^ (Holant.weight (complementWord s) * k) =
      rho ^ (Holant.weight s * k) := by
    calc
      _ = rho ^ ((Holant.weight (complementWord s) * k) % 8) := pow_mod_eight rho hr _
      _ = rho ^ ((Holant.weight s * k) % 8) := by congr 1; simpa only [Nat.mul_comm] using hw
      _ = _ := (pow_mod_eight rho hr _).symm
  rw [hp] at he
  exact mul_left_cancel₀ (pow_ne_zero _ hr0) he

include rho hr0 hr hc in
theorem support_even (hN : LocalAffine N) (s : W) (hs : N s ≠ 0) :
    Holant.weight s % 2 = 0 := by
  have hcs := support_complement N rho hr0 hc s hs
  have he := (hN s hs).fourth_power_eq s (complementWord s)
    ((twist_nonzero_iff s N s).mpr hs)
    ((twist_nonzero_iff s N (complementWord s)).mpr hcs)
  simp only [twist_apply, mul_pow, twistCoefficient_self_four,
    twistCoefficient_complement_self, one_mul] at he
  rw [complement_power N rho hr0 hr hc s 4 (weight_complement_mod_four s)] at he
  have hp : (-1 : AlgebraicComplex) ^ Holant.weight s = 1 :=
    mul_right_cancel₀ (pow_ne_zero _ hs) (by simpa only [one_mul] using he)
  rw [neg_one_pow_eq_pow_mod_two] at hp
  have hb := Nat.mod_lt (Holant.weight s) (by decide : 0 < 2)
  by_contra hz
  have ho : Holant.weight s % 2 = 1 := by omega
  rw [ho] at hp
  norm_num at hp

/-- A 256-case identity of small natural numbers, not a signature census. -/
theorem odd_overlap_cross_exponent : ∀ s t : W, Holant.weight s % 2 = 0 →
    overlap s t % 2 = 1 →
    (2 * (overlap s s + overlap s (complementWord t))) % 8 =
      (4 + 2 * (overlap s (complementWord s) + overlap s t)) % 8 := by
  decide

theorem odd_overlap_cross_coefficient (s t : W) (hs : Holant.weight s % 2 = 0)
    (ho : overlap s t % 2 = 1) :
    (twistCoefficient s s * twistCoefficient s (complementWord t)) ^ 2 =
      -(twistCoefficient s (complementWord s) * twistCoefficient s t) ^ 2 := by
  simp only [twistCoefficient_eq, ← pow_add, ← pow_mul]
  rw [Nat.mul_comm _ 2, pow_mod_eight zetaEight zetaEight_pow_eight,
    odd_overlap_cross_exponent s t hs ho]
  rw [← pow_mod_eight zetaEight zetaEight_pow_eight, pow_add, zetaEight_pow_four]
  rw [Nat.mul_comm _ 2]
  ring

include rho hr0 hr hc in
theorem support_orthogonal (hN : LocalAffine N) (s t : W)
    (hs : N s ≠ 0) (ht : N t ≠ 0) : overlap s t % 2 = 0 := by
  have hse := support_even N rho hr0 hr hc hN s hs
  have hte := support_even N rho hr0 hr hc hN t ht
  have hcs := support_complement N rho hr0 hc s hs
  have hct := support_complement N rho hr0 hc t ht
  have hcross := affine_complement_cross_square (localTwist s N) (hN s hs) s t
    ((twist_nonzero_iff s N s).mpr hs) ((twist_nonzero_iff s N t).mpr ht)
    ((twist_nonzero_iff s N (complementWord s)).mpr hcs)
    ((twist_nonzero_iff s N (complementWord t)).mpr hct)
  have hsq_s := complement_power N rho hr0 hr hc s 2 (weight_complement_mod_two s hse)
  have hsq_t := complement_power N rho hr0 hr hc t 2 (weight_complement_mod_two t hte)
  simp only [twist_apply, mul_pow] at hcross
  rw [hsq_s, hsq_t] at hcross
  have hp : (twistCoefficient s s * twistCoefficient s (complementWord t)) ^ 2 =
      (twistCoefficient s (complementWord s) * twistCoefficient s t) ^ 2 := by
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hs) (pow_ne_zero 2 ht))
    linear_combination hcross
  by_contra hz
  have ho : overlap s t % 2 = 1 := by have := Nat.mod_lt (overlap s t) (by decide : 0 < 2); omega
  have hb := odd_overlap_cross_coefficient s t hse ho
  have hzero : (twistCoefficient s (complementWord s) * twistCoefficient s t) ^ 2 = 0 := by
    linear_combination (hb - hp) / 2
  exact pow_ne_zero 2 (mul_ne_zero (twistCoefficient_ne_zero _ _) (twistCoefficient_ne_zero _ _)) hzero

end
end Holant.EightVertex.LocalAffineCollapse.Phase
