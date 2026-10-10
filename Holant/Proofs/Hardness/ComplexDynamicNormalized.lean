import Holant.Proofs.Hardness.ComplexDynamicExpansion

/-! Finite-size complex separation under a strict norm cone.  No real embedding
or phase restriction is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicNormalized
open ComplexDynamicExpansion

def A (δ : ℂ) : ℂ := (1-δ)/2
def B (δ : ℂ) : ℂ := (1+δ)/2
def x (ε δ : ℂ) : ℂ := (B δ+ε)/A δ
def y (ε δ : ℂ) : ℂ := (B δ-ε)/A δ
def z (ε δ : ℂ) : ℂ := x ε δ*y ε δ

private theorem size_budget {t : ℝ} {m n : ℕ} (ht : 0 < t)
    (hsmall : t < 1/(128*((m:ℝ)+1)^2)) (hn : n ≤ m) :
    t < 1/128 ∧ (n:ℝ)*t < 1/128 ∧ (n:ℝ)^2*t < 1/128 := by
  have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hnm : (n:ℝ) ≤ m := by exact_mod_cast hn
  have hd : 0 < 128*((m:ℝ)+1)^2 := by positivity
  have hh := (lt_div_iff₀ hd).mp hsmall
  have hb : ((m:ℝ)+1)^2*t < 1/128 := by nlinarith
  have hb1 : 1 ≤ ((m:ℝ)+1)^2 := by nlinarith
  have hbn : (n:ℝ) ≤ ((m:ℝ)+1)^2 := by nlinarith [sq_nonneg (m:ℝ)]
  have hbn2 : (n:ℝ)^2 ≤ ((m:ℝ)+1)^2 := by nlinarith
  exact ⟨lt_of_le_of_lt (by nlinarith [mul_le_mul_of_nonneg_right hb1 ht.le]) hb,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbn ht.le) hb,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbn2 ht.le) hb⟩

theorem A_nonzero {ε δ : ℂ} {m : ℕ} (hε : 0 < ‖ε‖)
    (hsmall : ‖ε‖ < 1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖ ≤ ‖ε‖^2/4) : A δ ≠ 0 := by
  have ht := (size_budget hε hsmall (n := 0) (by omega)).1
  have hd : ‖δ‖ < 1 := by nlinarith [norm_nonneg δ]
  intro ha
  have hz : 1-δ = 0 := by simpa only [A, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using ha
  have he : δ = 1 := (sub_eq_zero.mp hz).symm
  rw [he, norm_one] at hd
  linarith

private theorem cast_gap {i j : ℕ} (hij : i ≠ j) : (1:ℝ) ≤ ‖(i:ℂ)-(j:ℂ)‖ := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i:ℝ)+1 ≤ j := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hh : (j:ℝ)+1 ≤ i := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith

private theorem raw_ne_of_ne {ε δ : ℂ} {m i j : ℕ} (hε : 0 < ‖ε‖)
    (hsmall : ‖ε‖ < 1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖ ≤ ‖ε‖^2/4)
    (hij : i+j ≤ m) (hne : i ≠ j) :
    (1-δ)^(i+j) ≠ (1+δ+2*ε)^i * (1+δ-2*ε)^j := by
  obtain ⟨ht, hn, hn2⟩ := size_budget hε hsmall hij
  have hn0 : 0 ≤ ((i+j:ℕ):ℝ) := Nat.cast_nonneg _
  have hd : ‖δ‖ ≤ 3*‖ε‖ := by nlinarith [norm_nonneg δ]
  have hu : ‖δ+2*ε‖ ≤ 3*‖ε‖ := by
    have hh := norm_add_le δ (2*ε)
    norm_num [norm_mul] at hh
    nlinarith [norm_nonneg δ]
  have hv : ‖δ-2*ε‖ ≤ 3*‖ε‖ := by
    have hh := norm_sub_le δ (2*ε)
    norm_num [norm_mul] at hh
    nlinarith [norm_nonneg δ]
  have hs : ((i+j:ℕ):ℝ)*(3*‖ε‖) ≤ 1 := by linarith
  have hp := power_remainder (-δ) (i+j) (by positivity : 0 ≤ 3*‖ε‖)
    (by simpa using hd) hs
  have hq := mixed_remainder (δ+2*ε) (δ-2*ε) i j
    (by positivity : 0 ≤ 3*‖ε‖) hu hv hs
  intro he
  have he' : (1 + -δ)^(i+j) =
      (1+(δ+2*ε))^i * (1+(δ-2*ε))^j := by
    simpa only [sub_eq_add_neg, add_assoc] using he
  have hid : 2*((i:ℂ)-(j:ℂ))*ε =
      ((1 + -δ)^(i+j)-1-((i+j:ℕ):ℂ)*(-δ)) -
      ((1+(δ+2*ε))^i*(1+(δ-2*ε))^j-1-((i:ℂ)*(δ+2*ε)+(j:ℂ)*(δ-2*ε))) -
      2*((i+j:ℕ):ℂ)*δ := by
    rw [← he']
    push_cast
    ring
  have hnorm := norm_sub_le
    (((1 + -δ)^(i+j)-1-((i+j:ℕ):ℂ)*(-δ)) -
      ((1+(δ+2*ε))^i*(1+(δ-2*ε))^j-1-((i:ℂ)*(δ+2*ε)+(j:ℂ)*(δ-2*ε))))
    (2*((i+j:ℕ):ℂ)*δ)
  have hnorm' := norm_sub_le
    ((1 + -δ)^(i+j)-1-((i+j:ℕ):ℂ)*(-δ))
    ((1+(δ+2*ε))^i*(1+(δ-2*ε))^j-1-((i:ℂ)*(δ+2*ε)+(j:ℂ)*(δ-2*ε)))
  rw [← hid] at hnorm
  norm_num only [norm_mul, Complex.norm_ofNat, norm_natCast] at hnorm
  have hgap := cast_gap hne
  have hgap' : 2*‖ε‖ ≤ 2*‖(i:ℂ)-(j:ℂ)‖*‖ε‖ := by nlinarith
  have hsum : 2*‖ε‖ ≤ 18*((i+j:ℕ):ℝ)^2*‖ε‖^2 + 2*((i+j:ℕ):ℝ)*‖δ‖ := by
    nlinarith
  have hδ' := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2*((i+j:ℕ):ℝ))
  have hb1 := mul_lt_mul_of_pos_right hn hε
  have hb2 := mul_lt_mul_of_pos_right hn2 hε
  nlinarith

private theorem raw_ne_of_eq {ε δ : ℂ} {m i : ℕ} (hε : 0 < ‖ε‖)
    (hsmall : ‖ε‖ < 1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖ ≤ ‖ε‖^2/4)
    (hi : i ≤ m) (hipos : 0 < i) :
    (1-δ)^(i+i) ≠ (1+δ+2*ε)^i * (1+δ-2*ε)^i := by
  obtain ⟨ht, hn, hn2⟩ := size_budget hε hsmall hi
  have hi0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have hi1 : 1 ≤ (i:ℝ) := by exact_mod_cast hipos
  have hd : ‖δ‖ ≤ 1 := by nlinarith [norm_nonneg δ]
  have hd2 : ‖δ‖^2 ≤ ‖δ‖ := by nlinarith [norm_nonneg δ]
  let u : ℂ := 2*δ+δ^2-4*ε^2
  let v : ℂ := -(2*δ)+δ^2
  have hu : ‖u‖ ≤ 6*‖ε‖^2 := by
    have h1 := norm_sub_le (2*δ+δ^2) (4*ε^2)
    have h2 := norm_add_le (2*δ) (δ^2)
    norm_num [norm_mul, norm_pow] at h1 h2
    dsimp [u]
    nlinarith
  have hv : ‖v‖ ≤ 6*‖ε‖^2 := by
    have h1 := norm_add_le (-2*δ) (δ^2)
    norm_num [norm_mul, norm_pow] at h1
    dsimp [v]
    nlinarith
  have hs : (i:ℝ)*(6*‖ε‖^2) ≤ 1 := by
    have hh := mul_nonneg hi0 (show 0 ≤ ‖ε‖-‖ε‖^2 by nlinarith)
    nlinarith
  have hp := power_remainder u i (by positivity : 0 ≤ 6*‖ε‖^2) hu hs
  have hq := power_remainder v i (by positivity : 0 ≤ 6*‖ε‖^2) hv hs
  have hid : u-v = 4*(δ-ε^2) := by dsimp [u,v]; ring
  have hdiff : 3*‖ε‖^2 ≤ ‖u-v‖ := by
    have hh := norm_sub_norm_le (ε^2) δ
    rw [norm_sub_rev] at hh
    rw [hid]
    norm_num [norm_mul, norm_pow] at hh ⊢
    nlinarith
  have hlow : 3*‖ε‖^2 ≤ ‖(i:ℂ)*(u-v)‖ := by
    rw [norm_mul, norm_natCast]
    have hh := mul_le_mul_of_nonneg_left hdiff hi0
    nlinarith [sq_nonneg ‖ε‖]
  intro he
  have he' : (1+u)^i = (1+v)^i := by
    calc
      _ = (1+δ+2*ε)^i * (1+δ-2*ε)^i := by
        rw [← mul_pow]
        congr 1
        dsimp [u]
        ring
      _ = (1-δ)^(i+i) := he.symm
      _ = (1+v)^i := by
        rw [show i+i = 2*i by omega, pow_mul]
        congr 1
        dsimp [v]
        ring
  have hid' : (i:ℂ)*(u-v) = ((1+v)^i-1-(i:ℂ)*v) - ((1+u)^i-1-(i:ℂ)*u) := by
    rw [he']
    ring
  have hh := norm_sub_le ((1+v)^i-1-(i:ℂ)*v) ((1+u)^i-1-(i:ℂ)*u)
  rw [← hid'] at hh
  have hb : 3*‖ε‖^2 ≤ 72*(i:ℝ)^2*‖ε‖^4 := by nlinarith
  have hbudget : (i:ℝ)^2*‖ε‖^2 < 1/128 := by
    have hh := mul_lt_mul_of_pos_right hn2 hε
    nlinarith
  have hfinal := mul_lt_mul_of_pos_right hbudget (sq_pos_of_pos hε)
  nlinarith

/-- The equal exponent pair (1,1) needs only the strict norm cone. -/
theorem pair_coefficients_ne {ε δ : ℂ} (hε : 0 < ‖ε‖)
    (hδ : ‖δ‖ ≤ ‖ε‖^2/4) : (A δ)^2 ≠ (B δ+ε)*(B δ-ε) := by
  intro he
  have hid : ε^2-δ = (A δ)^2-(B δ+ε)*(B δ-ε) := by dsimp [A,B]; ring
  have heq : ε^2 = δ := sub_eq_zero.mp (by rw [hid, he, sub_self])
  have hn := congrArg norm heq
  rw [norm_pow] at hn
  nlinarith

/-- Homogeneous separation on every nonzero point of the bounded exponent grid.
The coefficient phases are arbitrary, and δ may be zero. -/
theorem coefficients_ne {ε δ : ℂ} {m i j : ℕ} (hε : 0 < ‖ε‖)
    (hsmall : ‖ε‖ < 1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖ ≤ ‖ε‖^2/4)
    (hij : i+j ≤ m) (hpos : 0 < i+j) :
    (A δ)^(i+j) ≠ (B δ+ε)^i * (B δ-ε)^j := by
  have hraw : (1-δ)^(i+j) ≠ (1+δ+2*ε)^i * (1+δ-2*ε)^j := by
    by_cases heq : i = j
    · subst j
      exact raw_ne_of_eq hε hsmall hδ (by omega) (by omega)
    · exact raw_ne_of_ne hε hsmall hδ hij heq
  have ha : 1-δ = 2*A δ := by dsimp [A]; ring
  have hx : 1+δ+2*ε = 2*(B δ+ε) := by dsimp [B]; ring
  have hy : 1+δ-2*ε = 2*(B δ-ε) := by dsimp [B]; ring
  intro he
  apply hraw
  rw [ha, hx, hy, mul_pow, mul_pow, mul_pow, he, pow_add]
  ring

/-- The desired normalized eigenratio differs from every unwanted bounded mode. -/
theorem ratios_ne_one {ε δ : ℂ} {m i j : ℕ} (hε : 0 < ‖ε‖)
    (hsmall : ‖ε‖ < 1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖ ≤ ‖ε‖^2/4)
    (hij : i+j ≤ m) (hpos : 0 < i+j) : (x ε δ)^i * (y ε δ)^j ≠ 1 := by
  have ha := A_nonzero hε hsmall hδ
  intro he
  apply coefficients_ne hε hsmall hδ hij hpos
  dsimp [x,y] at he
  rw [div_pow, div_pow, ← mul_div_mul_comm, ← pow_add] at he
  exact ((div_eq_one_iff_eq (pow_ne_zero _ ha)).mp he).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexDynamicNormalized
