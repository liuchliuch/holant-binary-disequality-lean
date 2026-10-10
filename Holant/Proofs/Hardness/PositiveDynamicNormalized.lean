import Holant.Proofs.Hardness.ThreeModeAnnihilator

/-! Finite-size separation inside the positive self-dual triangle.  These
lemmas concern a bounded exponent grid only, never infinite nonresonance. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicNormalized

/-- Normalized pair coefficients of the even chain, after its port swap. -/
def A (δ : ℝ) : ℝ := (1-δ)/2
def B (δ : ℝ) : ℝ := (1+δ)/2
def x (ε δ : ℝ) : ℝ := (B δ+ε)/A δ
def y (ε δ : ℝ) : ℝ := (B δ-ε)/A δ
def z (ε δ : ℝ) : ℝ := x ε δ*y ε δ

/-- Loose constants leave room for a uniform, linear-size stage length. -/
theorem bounds {ε δ : ℝ} (hε : 0<ε) (hsmall : ε<1/128)
    (hδ : 0≤δ) (hδε : δ<ε^2) :
    1<x ε δ ∧ 0<y ε δ ∧ y ε δ<1 ∧ 0<z ε δ ∧ z ε δ<1 ∧
    2*ε≤x ε δ-1 ∧ (1-z ε δ)*x ε δ<64*ε^2 := by
  have hε1 : ε<1 := by linarith
  have hεsq : ε^2<ε := by nlinarith
  have hδ1 : δ<1/2 := by nlinarith
  have ha : 1/4<A δ := by dsimp [A]; linarith
  have ha0 : 0<A δ := by linarith
  have hb : B δ+ε<1 := by dsimp [B]; nlinarith
  have hy0 : 0<y ε δ := (div_pos (by dsimp [B]; nlinarith) ha0)
  have hx : 1<x ε δ := (lt_div_iff₀ ha0).mpr (by dsimp [A,B]; linarith)
  have hy : y ε δ<1 := (div_lt_one ha0).mpr (by dsimp [A,B]; nlinarith)
  have hz0 : 0<z ε δ := mul_pos (by linarith) hy0
  have hzid : (1-z ε δ)*(A δ)^2=ε^2-δ := by
    dsimp [z,x,y]
    field_simp
    dsimp [A,B]
    ring
  have hgap0 : 0<1-z ε δ := by
    have : 0<(1-z ε δ)*(A δ)^2 := by rw [hzid]; linarith
    exact pos_of_mul_pos_left this (sq_nonneg _)
  have hz : z ε δ<1 := by linarith
  have hxbound : x ε δ<4 := (div_lt_iff₀ ha0).mpr (by linarith)
  have hxgap : 2*ε≤x ε δ-1 := by
    have h : 2*ε+1≤x ε δ := by
      apply (le_div_iff₀ ha0).mpr
      dsimp [A,B]
      nlinarith [mul_nonneg hε.le hδ]
    linarith
  have hzgap : 1-z ε δ<16*ε^2 := by
    have hasq : 1/16<(A δ)^2 := by nlinarith
    nlinarith [mul_pos hgap0 (sub_pos.mpr hasq)]
  refine ⟨hx,hy0,hy,hz0,hz,hxgap,?_⟩
  nlinarith [mul_pos hgap0 (sub_pos.mpr hxbound)]

/-- The loss from at most m factors z is smaller than the gain from one x. -/
theorem x_mul_z_pow_gt_one {ε δ : ℝ} {m j : ℕ}
    (hε : 0<ε) (hsmall : ε<1/(128*((m:ℝ)+1)))
    (hδ : 0≤δ) (hδε : δ<ε^2) (hj : j≤m) : 1<x ε δ*(z ε δ)^j := by
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hsmall' : ε<1/128 := by
    have hd : (0:ℝ)<128*((m:ℝ)+1) := by positivity
    have h := (lt_div_iff₀ hd).mp hsmall
    nlinarith [mul_nonneg hε.le hm]
  obtain ⟨hx,_,_,hz0,hz,hxgap,hzgap⟩ := bounds hε hsmall' hδ hδε
  have hd : (0:ℝ)<128*((m:ℝ)+1) := by positivity
  have hbudget := (lt_div_iff₀ hd).mp hsmall
  have hjr : (j:ℝ)≤m := by exact_mod_cast hj
  have hloss : (j:ℝ)*(1-z ε δ)*x ε δ<ε/2 := by
    have hj0 : 0≤(j:ℝ) := Nat.cast_nonneg _
    have h1 : (j:ℝ)*((1-z ε δ)*x ε δ)≤(m:ℝ)*(64*ε^2) :=
      mul_le_mul hjr hzgap.le (by positivity) hm
    have h2 : (m:ℝ)*(64*ε^2)<ε/2 := by
      nlinarith [mul_pos hε (sub_pos.mpr hbudget)]
    nlinarith
  have hbern := one_add_mul_sub_le_pow (by linarith : -1≤z ε δ) j
  have hmul := mul_le_mul_of_nonneg_left hbern (by linarith : 0≤x ε δ)
  nlinarith

/-- A direct finite grid separation statement for the normalized eigenratios. -/
theorem ratios_ne_one {ε δ : ℝ} {m i j : ℕ}
    (hε : 0<ε) (hsmall : ε<1/(128*((m:ℝ)+1)))
    (hδ : 0≤δ) (hδε : δ<ε^2) (hij : i + j ≤ m) (hpos : 0 < i + j) :
    (x ε δ)^i*(y ε δ)^j≠1 := by
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hsmall' : ε<1/128 := by
    have hd : (0:ℝ)<128*((m:ℝ)+1) := by positivity
    have h := (lt_div_iff₀ hd).mp hsmall
    nlinarith [mul_nonneg hε.le hm]
  obtain ⟨hx,hy0,hy,hz0,hz,_,_⟩ := bounds hε hsmall' hδ hδε
  rcases lt_trichotomy i j with hlt|heq|hgt
  · have he : (x ε δ)^i*(y ε δ)^j=(z ε δ)^i*(y ε δ)^(j-i) := by
      rw [z,mul_pow,mul_assoc,←pow_add, Nat.add_sub_of_le hlt.le]
    rw [he]
    have hp : (y ε δ)^(j-i)<1 := pow_lt_one₀ hy0.le hy (by omega)
    have hzle : (z ε δ)^i≤1 := pow_le_one₀ hz0.le hz.le
    exact ne_of_lt (lt_of_le_of_lt (mul_le_of_le_one_left (pow_nonneg hy0.le _) hzle) hp)
  · subst j
    have he : (x ε δ)^i*(y ε δ)^i=(z ε δ)^i := by rw [z,mul_pow]
    rw [he]
    exact ne_of_lt (pow_lt_one₀ hz0.le hz (by omega))
  · have he : (x ε δ)^i*(y ε δ)^j=(x ε δ)^(i-j)*(z ε δ)^j := by
      rw [z,mul_pow,←mul_assoc,←pow_add, Nat.sub_add_cancel hgt.le]
    rw [he]
    have hxle : x ε δ≤(x ε δ)^(i-j) := by
      simpa only [pow_one] using pow_le_pow_right₀ hx.le (by omega : 1 ≤ i - j)
    have hb := x_mul_z_pow_gt_one hε hsmall hδ hδε (by omega : j≤m)
    exact ne_of_gt (lt_of_lt_of_le hb (mul_le_mul_of_nonneg_right hxle (pow_nonneg hz0.le _)))

/-- Homogeneous version: the desired coefficient differs from every bounded
unwanted exponent pair, including when δ is zero. -/
theorem coefficients_ne {ε δ : ℝ} {m i j : ℕ}
    (hε : 0<ε) (hsmall : ε<1/(128*((m:ℝ)+1)))
    (hδ : 0≤δ) (hδε : δ<ε^2) (hij : i + j ≤ m) (hpos : 0 < i + j) :
    (A δ)^(i+j)≠(B δ+ε)^i*(B δ-ε)^j := by
  have hm : 0≤(m:ℝ) := Nat.cast_nonneg _
  have hd : (0:ℝ)<128*((m:ℝ)+1) := by positivity
  have hb := (lt_div_iff₀ hd).mp hsmall
  have he1 : ε<1/128 := by nlinarith [mul_nonneg hε.le hm]
  have he2 : ε^2<1/2 := by nlinarith
  have ha : A δ≠0 := by dsimp [A]; linarith
  intro he
  apply ratios_ne_one hε hsmall hδ hδε hij hpos
  dsimp [x,y]
  rw [div_pow,div_pow,←mul_div_mul_comm,←pow_add,←he]
  exact div_self (pow_ne_zero _ ha)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicNormalized
