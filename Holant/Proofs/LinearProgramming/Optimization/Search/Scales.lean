import Mathlib.Tactic

/-!
Explicit rational axial/transverse scales, including the inflation charged for
the computed square-root approximation. The contraction is deliberately weak
(order n^-3), but is proved quantitatively rather than asserted as an oracle.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Scales

def axial (n : ℕ) : ℚ := (n:ℚ)/(n+1)
def transverse (n : ℕ) : ℚ := 1+1/(n:ℚ)^2
def inflation (n : ℕ) : ℚ := 1+1/(16*(n:ℚ)^4)
def precision (n : ℕ) : ℕ := 512*n^4
def contraction (n : ℕ) : ℚ := 1-1/(2*((n:ℚ)^3+1))

theorem axial_pos (n : ℕ) (hn : 0<n) : 0<axial n := by unfold axial; positivity
theorem transverse_pos (n : ℕ) : 0<transverse n := by unfold transverse; positivity
theorem inflation_pos (n : ℕ) : 0 < inflation n := by unfold inflation; positivity
theorem precision_pos (n : ℕ) (hn : 0<n) : 0<precision n := by unfold precision; positivity
theorem contraction_pos (n : ℕ) : 0<contraction n := by
  have h : (0:ℚ)≤(n:ℚ)^3 := by positivity
  unfold contraction
  have : 1/(2*((n:ℚ)^3+1))<1 := (div_lt_one (by positivity)).mpr (by linarith)
  linarith
theorem contraction_lt_one (n : ℕ) : contraction n<1 := by
  unfold contraction
  have : (0:ℚ)<1/(2*((n:ℚ)^3+1)) := by positivity
  linarith

/-- Reciprocal Bernoulli bound proved by induction, avoiding any logarithm or
unproved exponential-volume estimate. -/
theorem pow_weight (x : ℚ) (hx : 0≤x) (k : ℕ) :
    (1+x)^k*(1-(k:ℚ)*x)≤1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : (1+x)*(1-((k:ℚ)+1)*x)≤1-(k:ℚ)*x := by
      have : 0≤((k:ℚ)+1)*x^2 := by positivity
      nlinarith
    calc
      (1+x)^(k+1)*(1-((k+1:ℕ):ℚ)*x) =
          (1+x)^k*((1+x)*(1-((k:ℚ)+1)*x)) := by push_cast; ring
      _ ≤ (1+x)^k*(1-(k:ℚ)*x) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg (by linarith) _)
      _ ≤ 1 := ih

theorem pow_upper (x : ℚ) (hx : 0≤x) (k : ℕ) (hk : (k:ℚ)*x<1) :
    (1+x)^k≤1/(1-(k:ℚ)*x) :=
  (le_div_iff₀ (by linarith)).mpr (pow_weight x hx k)

theorem transverse_bound (n : ℕ) (hn : 2≤n) :
    transverse n^(n-1)≤(n:ℚ)^2/((n:ℚ)^2-n+1) := by
  have hN : (2:ℚ)≤n := by exact_mod_cast hn
  have hne : (n:ℚ)≠0 := by linarith
  have hm : ((n-1:ℕ):ℚ)=(n:ℚ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hsmall : ((n-1:ℕ):ℚ)*(1/(n:ℚ)^2)<1 := by
    rw [hm]
    rw [mul_one_div]
    exact (div_lt_one (by positivity : (0:ℚ)<(n:ℚ)^2)).mpr (by nlinarith)
  have hb := pow_upper (1/(n:ℚ)^2) (by positivity) (n-1) hsmall
  have he : 1/(1-((n-1:ℕ):ℚ)*(1/(n:ℚ)^2))=
      (n:ℚ)^2/((n:ℚ)^2-n+1) := by
    rw [hm]
    field_simp
    <;> ring
  simpa only [transverse,he] using hb

theorem axial_transverse_bound (n : ℕ) (hn : 2≤n) :
    axial n*transverse n^(n-1)≤(n:ℚ)^3/((n:ℚ)^3+1) := by
  have hN : (2:ℚ)≤n := by exact_mod_cast hn
  have hd : (0:ℚ)<(n:ℚ)^2-n+1 := by nlinarith
  calc
    _ ≤ axial n*((n:ℚ)^2/((n:ℚ)^2-n+1)) :=
      mul_le_mul_of_nonneg_left (transverse_bound n hn) (axial_pos n (by omega)).le
    _ = (n:ℚ)^3/((n:ℚ)^3+1) := by
      unfold axial
      rw [div_mul_div_comm]
      congr 1 <;> ring

theorem inflation_bound (n : ℕ) (hn : 2≤n) :
    inflation n^n≤16*(n:ℚ)^3/(16*(n:ℚ)^3-1) := by
  have hN : (2:ℚ)≤n := by exact_mod_cast hn
  have hne : (n:ℚ)≠0 := by linarith
  have hcube : (1:ℚ)≤(n:ℚ)^3 := one_le_pow₀ (by linarith)
  have hs : (n:ℚ)*(1/(16*(n:ℚ)^4))=1/(16*(n:ℚ)^3) := by field_simp <;> ring
  have hsmall : (n:ℚ)*(1/(16*(n:ℚ)^4))<1 := by
    rw [hs]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hb := pow_upper (1/(16*(n:ℚ)^4)) (by positivity) n hsmall
  have he : 1/(1-(n:ℚ)*(1/(16*(n:ℚ)^4)))=
      16*(n:ℚ)^3/(16*(n:ℚ)^3-1) := by
    rw [hs]
    field_simp
    <;> ring
  simpa only [inflation,he] using hb

theorem volume_factor (n : ℕ) (hn : 2≤n) :
    inflation n^n*(axial n*transverse n^(n-1))≤contraction n := by
  have hN : (2:ℚ)≤n := by exact_mod_cast hn
  have hcube : (1:ℚ)≤(n:ℚ)^3 := one_le_pow₀ (by linarith)
  have hd : (0:ℚ)<16*(n:ℚ)^3-1 := by linarith
  have he : (0:ℚ)<(n:ℚ)^3+1 := by positivity
  calc
    _ ≤ (16*(n:ℚ)^3/(16*(n:ℚ)^3-1))*((n:ℚ)^3/((n:ℚ)^3+1)) :=
      mul_le_mul (inflation_bound n hn) (axial_transverse_bound n hn)
        (mul_nonneg (axial_pos n (by omega)).le
          (pow_nonneg (transverse_pos n).le _)) (by positivity)
    _ ≤ contraction n := by
      have hpoly : (32:ℚ)*(n:ℚ)^6≤(2*(n:ℚ)^3+1)*(16*(n:ℚ)^3-1) := by
        nlinarith
      have hfrac : (16*(n:ℚ)^6)/(16*(n:ℚ)^3-1)≤(2*(n:ℚ)^3+1)/2 := by
        apply (div_le_div_iff₀ hd (by norm_num : (0:ℚ)<2)).mpr
        nlinarith [hpoly]
      calc
        _ = ((16*(n:ℚ)^6)/(16*(n:ℚ)^3-1))/((n:ℚ)^3+1) := by ring
        _ ≤ ((2*(n:ℚ)^3+1)/2)/((n:ℚ)^3+1) :=
          div_le_div_of_nonneg_right hfrac he.le
        _ = contraction n := by unfold contraction; field_simp <;> ring

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.Scales
