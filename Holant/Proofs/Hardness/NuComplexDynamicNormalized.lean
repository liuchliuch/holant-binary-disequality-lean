import Holant.Proofs.Hardness.ComplexDynamicNormalized

/-! Signed normalized separation for the b-a dominant branch. Odd total
exponents are separated by a finite product bound around one; even total
exponents use the existing strict norm-cone separation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.NuComplexDynamicNormalized
open ComplexDynamicExpansion ComplexDynamicNormalized

private theorem size_budget {t : ℝ} {m n : ℕ} (ht : 0 < t)
    (hsmall : t < 1/(128*((m:ℝ)+1)^2)) (hn : n ≤ m) :
    t < 1/128 ∧ (n:ℝ)*t < 1/128 := by
  have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hnm : (n:ℝ) ≤ m := by exact_mod_cast hn
  have hh := (lt_div_iff₀ (by positivity : 0 < 128*((m:ℝ)+1)^2)).mp hsmall
  have hb : ((m:ℝ)+1)^2*t < 1/128 := by nlinarith
  have hb1 : 1 ≤ ((m:ℝ)+1)^2 := by nlinarith
  have hbn : (n:ℝ) ≤ ((m:ℝ)+1)^2 := by nlinarith [sq_nonneg (m:ℝ)]
  exact ⟨lt_of_le_of_lt (by nlinarith [mul_le_mul_of_nonneg_right hb1 ht.le]) hb,
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hbn ht.le) hb⟩

/-- A finite complex product stays within 1/4 of one under a small total budget. -/
theorem product_near_one (l : List ℂ) {s : ℝ} (hs : 0≤s)
    (hl : ∀u∈l, ‖u‖≤s) (hsmall : (l.length:ℝ)*s<1/8) :
    ‖(l.map (fun u=>1+u)).prod-1‖<1/4 := by
  have hn : 0≤(l.length:ℝ) := Nat.cast_nonneg _
  have hp := product_remainder l hs hl (by linarith)
  have hsum := norm_sum_le_length_mul l hs hl
  have hh := norm_add_le ((l.map (fun u=>1+u)).prod-1-l.sum) l.sum
  have hid : (l.map (fun u=>1+u)).prod-1-l.sum+l.sum =
      (l.map (fun u=>1+u)).prod-1 := by ring
  rw [hid] at hh
  have hb : ((l.length:ℝ)*s)^2 < (1/8:ℝ)^2 := by
    nlinarith [mul_nonneg hn hs]
  nlinarith

private theorem raw_ne_neg {ε δ : ℂ} {m i j : ℕ} (hε : 0<‖ε‖)
    (hsmall : ‖ε‖<1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖≤‖ε‖^2/4)
    (hij : i+j≤m) :
    (1+δ+2*ε)^i*(1+δ-2*ε)^j ≠ -(1-δ)^(i+j) := by
  obtain ⟨ht,hn⟩ := size_budget hε hsmall hij
  have hd : ‖δ‖≤3*‖ε‖ := by nlinarith [norm_nonneg δ]
  have hu : ‖δ+2*ε‖≤3*‖ε‖ := by
    have hh := norm_add_le δ (2*ε)
    norm_num [norm_mul] at hh
    nlinarith [norm_nonneg δ]
  have hv : ‖δ-2*ε‖≤3*‖ε‖ := by
    have hh := norm_sub_le δ (2*ε)
    norm_num [norm_mul] at hh
    nlinarith [norm_nonneg δ]
  have hP := product_near_one (List.replicate (i+j) (-δ))
    (by positivity : 0≤3*‖ε‖)
    (fun u hu=>by rcases List.mem_replicate.mp hu with ⟨_,rfl⟩; simpa using hd)
    (by simpa using (show ((i+j:ℕ):ℝ)*(3*‖ε‖)<1/8 by linarith))
  have hQ := product_near_one (List.replicate i (δ+2*ε) ++ List.replicate j (δ-2*ε))
    (by positivity : 0≤3*‖ε‖)
    (fun u hh=>by
      rcases List.mem_append.mp hh with hh|hh
      · rcases List.mem_replicate.mp hh with ⟨_,rfl⟩; exact hu
      · rcases List.mem_replicate.mp hh with ⟨_,rfl⟩; exact hv)
    (by simp only [List.length_append,List.length_replicate ]
        linarith)
  have hP' : ‖(1-δ)^(i+j)-1‖<1/4 := by simpa only [List.map_replicate,List.prod_replicate,sub_eq_add_neg] using hP
  have hQ' : ‖(1+δ+2*ε)^i*(1+δ-2*ε)^j-1‖<1/4 := by
    simpa only [List.map_append,List.map_replicate,List.prod_append,List.prod_replicate,sub_eq_add_neg,add_assoc] using hQ
  intro he
  have hh := norm_add_le ((1-δ)^(i+j)-1)
    ((1+δ+2*ε)^i*(1+δ-2*ε)^j-1)
  rw [he] at hh
  have hid : (1-δ)^(i+j)-1+(-(1-δ)^(i+j)-1)=(-2:ℂ) := by ring
  rw [hid] at hh
  norm_num at hh
  rw [he] at hQ'
  linarith

/-- The unsigned ratios cannot equal -1, including at the zero exponent pair. -/
theorem ratios_ne_neg_one {ε δ : ℂ} {m i j : ℕ} (hε : 0<‖ε‖)
    (hsmall : ‖ε‖<1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖≤‖ε‖^2/4)
    (hij : i+j≤m) : (x ε δ)^i*(y ε δ)^j≠-1 := by
  have ha := A_nonzero hε hsmall hδ
  intro he
  have he' : (B δ+ε)^i*(B δ-ε)^j = -(A δ)^(i+j) := by
    dsimp [x,y] at he
    rw [div_pow,div_pow,←mul_div_mul_comm,←pow_add] at he
    have hh := (div_eq_iff (pow_ne_zero (i+j) ha)).mp he
    simpa using hh
  apply raw_ne_neg hε hsmall hδ hij
  have ha' : 1-δ=2*A δ := by dsimp [A]; ring
  have hx : 1+δ+2*ε=2*(B δ+ε) := by dsimp [B]; ring
  have hy : 1+δ-2*ε=2*(B δ-ε) := by dsimp [B]; ring
  rw [ha',hx,hy,mul_pow,mul_pow,mul_pow,pow_add]
  calc
    _ = (2:ℂ)^i*2^j*((B δ+ε)^i*(B δ-ε)^j) := by ring
    _ = _ := by rw [he']; ring

/-- The actual signed eigenratios separate every nonzero bounded grid point. -/
theorem ratios_ne_one {ε δ : ℂ} {m i j : ℕ} (hε : 0<‖ε‖)
    (hsmall : ‖ε‖<1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖≤‖ε‖^2/4)
    (hij : i+j≤m) (hpos : 0 < i + j) : (-x ε δ)^i*(-y ε δ)^j≠1 := by
  have hid : (-x ε δ)^i*(-y ε δ)^j = (-1:ℂ)^(i+j)*((x ε δ)^i*(y ε δ)^j) := by
    rw [pow_add]
    rw [show -x ε δ = (-1:ℂ)*x ε δ by ring,
      show -y ε δ = (-1:ℂ)*y ε δ by ring, mul_pow, mul_pow]
    ring
  rw [hid]
  rcases Nat.even_or_odd (i+j) with he|ho
  · rw [he.neg_one_pow,one_mul]
    exact ComplexDynamicNormalized.ratios_ne_one hε hsmall hδ hij hpos
  · rw [ho.neg_one_pow,neg_one_mul]
    intro hh
    exact ratios_ne_neg_one hε hsmall hδ hij (by linear_combination -hh)

/-- Homogeneous signed separation in normalized coordinates. -/
theorem coefficients_ne {ε δ : ℂ} {m i j : ℕ} (hε : 0<‖ε‖)
    (hsmall : ‖ε‖<1/(128*((m:ℝ)+1)^2)) (hδ : ‖δ‖≤‖ε‖^2/4)
    (hij : i+j≤m) (hpos : 0 < i + j) :
    (-A δ)^(i+j)≠(B δ+ε)^i*(B δ-ε)^j := by
  have ha := A_nonzero hε hsmall hδ
  intro he
  apply ratios_ne_one hε hsmall hδ hij hpos
  have hx : -x ε δ = (B δ+ε)/(-A δ) := by dsimp [x]; rw [div_neg]
  have hy : -y ε δ = (B δ-ε)/(-A δ) := by dsimp [y]; rw [div_neg]
  rw [hx,hy,div_pow,div_pow,←mul_div_mul_comm,←pow_add,←he]
  exact div_self (pow_ne_zero _ (neg_ne_zero.mpr ha))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.NuComplexDynamicNormalized
