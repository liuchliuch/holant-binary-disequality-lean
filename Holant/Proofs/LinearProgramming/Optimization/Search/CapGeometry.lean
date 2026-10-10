import Holant.Proofs.LinearProgramming.Optimization.Search.Scales
import Holant.Proofs.LinearProgramming.Optimization.Search.NormApprox

/-!
Containment of a central half-ball under the explicit rational semiaxes.
The second theorem includes the error of the integer-square-root normalizer.
Here t is the axial coordinate and q the squared transverse coordinate; the
factor-matrix connection in Projection establishes these from an actual cut.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.CapGeometry

/-- A scalar, dimension-independent central-cap calculation. -/
theorem cap_bound (a b h t q : ℝ) (ha : 0<a) (hab : a≤b)
    (hah : a=1-h) (hend : 1/b^2+h^2/a^2≤1)
    (ht : -1≤t ∧ t≤0) (hq : 0≤q) (hball : q+t^2≤1) :
    q/b^2+(t+h)^2/a^2≤1 := by
  have hb : 0<b := ha.trans_le hab
  have hU : 0≤1/b^2 := by positivity
  have hUV : 1/b^2≤1/a^2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ha) (by nlinarith)
  have hleft : (h-1)^2*(1/a^2)=1 := by
    have hsq : (h-1)^2=a^2 := by
      rw [show h-1=-a by linarith]
      ring
    rw [hsq,one_div,mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt ha))]
  have hcross : t*(t+1)*(1/a^2-1/b^2)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg ht.2 (by linarith)) (by linarith)
  calc
    q/b^2+(t+h)^2/a^2 ≤ (1-t^2)*(1/b^2)+(t+h)^2*(1/a^2) := by
      have hm : q*(1/b^2)≤(1-t^2)*(1/b^2) :=
        mul_le_mul_of_nonneg_right (show q≤1-t^2 by linarith) hU
      simp only [div_eq_mul_inv,one_div,one_mul] at hm ⊢
      linarith
    _ = (-t)*((h-1)^2*(1/a^2))+(t+1)*(1/b^2+h^2/a^2)+
        t*(t+1)*(1/a^2-1/b^2) := by ring
    _ ≤ (-t)*1+(t+1)*1 := by
      rw [hleft]
      have hm := mul_le_mul_of_nonneg_left hend (show 0≤t+1 by linarith)
      linarith
    _ = 1 := by ring

theorem scales_endpoint (n : ℕ) (hn : 2≤n) :
    1/(Scales.transverse n:ℝ)^2+
      (1/((n:ℝ)+1))^2/(Scales.axial n:ℝ)^2≤1 := by
  have hN : (2:ℝ)≤n := by exact_mod_cast hn
  have hne : (n:ℝ)≠0 := by linarith
  have hplus : (n:ℝ)+1≠0 := by linarith
  have ha : (0:ℝ)<(Scales.axial n:ℝ) := by exact_mod_cast Scales.axial_pos n (by omega)
  have hb : (0:ℝ)<(Scales.transverse n:ℝ) := by exact_mod_cast Scales.transverse_pos n
  have h2 : (4:ℝ)≤(n:ℝ)^2 := by nlinarith
  have h4 : 4*(n:ℝ)^2≤(n:ℝ)^4 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (n:ℝ))]
  have hid : (Scales.transverse n:ℝ)^2*((Scales.axial n:ℝ)^2-
      (1/((n:ℝ)+1))^2)-(Scales.axial n:ℝ)^2 =
      ((n:ℝ)^4-(n:ℝ)^2-1)/((n:ℝ)^4*((n:ℝ)+1)^2) := by
    simp only [Scales.transverse,Scales.axial,Rat.cast_add,Rat.cast_div,
      Rat.cast_one,Rat.cast_pow,Rat.cast_natCast]
    field_simp
    <;> ring
  have hprod : (Scales.axial n:ℝ)^2≤(Scales.transverse n:ℝ)^2*
      ((Scales.axial n:ℝ)^2-(1/((n:ℝ)+1))^2) := by
    have : 0≤((n:ℝ)^4-(n:ℝ)^2-1)/((n:ℝ)^4*((n:ℝ)+1)^2) :=
      div_nonneg (by nlinarith) (by positivity)
    linarith [hid]
  calc
    _ = ((Scales.axial n:ℝ)^2+(1/((n:ℝ)+1))^2*(Scales.transverse n:ℝ)^2)/
        ((Scales.axial n:ℝ)^2*(Scales.transverse n:ℝ)^2) := by field_simp <;> ring
    _ ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith [hprod])

theorem ideal_cap (n : ℕ) (hn : 2≤n) (t q : ℝ)
    (ht : -1≤t ∧ t≤0) (hq : 0≤q) (hball : q+t^2≤1) :
    q/(Scales.transverse n:ℝ)^2+
      (t+1/((n:ℝ)+1))^2/(Scales.axial n:ℝ)^2≤1 := by
  have hN : (2:ℝ)≤n := by exact_mod_cast hn
  have ha : (0:ℝ)<(Scales.axial n:ℝ) := by exact_mod_cast Scales.axial_pos n (by omega)
  have hah : (Scales.axial n:ℝ)=1-1/((n:ℝ)+1) := by
    simp only [Scales.axial,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
    field_simp
    <;> ring
  have hab : (Scales.axial n:ℝ)≤(Scales.transverse n:ℝ) := by
    rw [hah]
    have : (1:ℝ)≤(Scales.transverse n:ℝ) := by
      simp only [Scales.transverse,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast]
      have : (0:ℝ)≤1/(n:ℝ)^2 := by positivity
      linarith
    have : (0:ℝ)≤1/((n:ℝ)+1) := by positivity
    linarith
  exact cap_bound _ _ _ _ _ ha hab hah (scales_endpoint n hn) ht hq hball

theorem inflated_square (A b e eta : ℝ) (hA : 0≤A) (hball : A+b^2≤1)
    (heta : 0≤eta) (he : |e|≤eta) : A+(b+e)^2≤(1+eta)^2 := by
  have hb : |b|≤1 := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have he' := abs_le.mp he
  have he2 : e^2≤eta^2 := by nlinarith
  have hbe : b*e≤eta := calc
    _ ≤ |b*e| := le_abs_self _
    _ = |b| * |e| := abs_mul _ _
    _ ≤ 1*eta := mul_le_mul hb he (abs_nonneg _) (by norm_num)
    _ = eta := one_mul _
  nlinarith

/-- Normalization error for the actual `NormApprox.value`, without taking an
approximation certificate or a square-root oracle as an argument. -/
theorem normalized_shift (s : ℚ) (hs : 0<s) (T : ℕ) (hT : 0<T) :
    1-1/(T:ℝ) ≤ Real.sqrt (s:ℝ)/(NormApprox.value s T:ℝ) ∧
    Real.sqrt (s:ℝ)/(NormApprox.value s T:ℝ)≤1 := by
  have ha : (0:ℝ)<(NormApprox.value s T:ℝ) := by exact_mod_cast NormApprox.value_pos s T hT
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  obtain ⟨hl,hu⟩ := NormApprox.bounds s hs T hT
  rw [show (1+1/(T:ℝ))*Real.sqrt (s:ℝ)=
    Real.sqrt (s:ℝ)+Real.sqrt (s:ℝ)/(T:ℝ) by ring] at hu
  have he : (NormApprox.value s T:ℝ)-Real.sqrt (s:ℝ)≤
      (NormApprox.value s T:ℝ)/(T:ℝ) := by
    have hm := div_le_div_of_nonneg_right hl hT'.le
    linarith
  constructor
  · apply (le_div_iff₀ ha).mpr
    rw [show (1-1/(T:ℝ))*(NormApprox.value s T:ℝ)=
      (NormApprox.value s T:ℝ)-(NormApprox.value s T:ℝ)/(T:ℝ) by ring]
    linarith
  · exact (div_le_one ha).mpr hl

/-- The actual computed normalizer preserves the entire central cap after
the explicit inflation. In particular the query center need not be feasible.
This accounts for square-root approximation, not for future storage rounding.
-/
theorem rounded_cap (n : ℕ) (hn : 2≤n) (s : ℚ) (hs : 0<s) (t q : ℝ)
    (ht : -1≤t ∧ t≤0) (hq : 0≤q) (hball : q+t^2≤1) :
    q/(Scales.transverse n:ℝ)^2+
      (t+Real.sqrt (s:ℝ)/(((n:ℝ)+1)*(NormApprox.value s (Scales.precision n):ℝ)))^2/
        (Scales.axial n:ℝ)^2 ≤ (Scales.inflation n:ℝ)^2 := by
  let z := Real.sqrt (s:ℝ)/(NormApprox.value s (Scales.precision n):ℝ)
  let eta := (Scales.inflation n:ℝ)-1
  have hN : (2:ℝ)≤n := by exact_mod_cast hn
  have hpos : (0:ℝ)<n := by linarith
  have hne : (n:ℝ)≠0 := ne_of_gt hpos
  have hplus : (n:ℝ)+1≠0 := by linarith
  have ha : (Scales.axial n:ℝ)≠0 := by
    exact_mod_cast ne_of_gt (Scales.axial_pos n (by omega))
  have hT : 0<Scales.precision n := Scales.precision_pos n (by omega)
  have hz := normalized_shift s hs (Scales.precision n) hT
  change 1-1/(Scales.precision n:ℝ)≤z ∧ z≤1 at hz
  have herr : |z-1|≤1/(Scales.precision n:ℝ) := by
    rw [abs_of_nonpos (by linarith : z-1≤0)]
    linarith [hz.1]
  have heta : eta=1/(16*(n:ℝ)^4) := by
    simp [eta,Scales.inflation]
  have hprec : (Scales.precision n:ℝ)=512*(n:ℝ)^4 := by simp [Scales.precision]
  have hsmall : (1/(Scales.precision n:ℝ))/(n:ℝ)≤eta := by
    rw [heta,hprec,div_div]
    apply one_div_le_one_div_of_le (by positivity)
    have : 0≤(512*(n:ℝ)-16)*(n:ℝ)^4 := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have he : |(z-1)/(n:ℝ)|≤eta := by
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_div_of_nonneg_right herr hpos.le).trans hsmall
  have hE := inflated_square (q/(Scales.transverse n:ℝ)^2)
    ((t+1/((n:ℝ)+1))/(Scales.axial n:ℝ)) ((z-1)/(n:ℝ)) eta
    (by positivity) (by simpa only [div_pow] using ideal_cap n hn t q ht hq hball)
    (by rw [heta]; positivity) he
  have hid : (t+1/((n:ℝ)+1))/(Scales.axial n:ℝ)+(z-1)/(n:ℝ)=
      (t+Real.sqrt (s:ℝ)/(((n:ℝ)+1)*(NormApprox.value s (Scales.precision n):ℝ)))/
        (Scales.axial n:ℝ) := by
    simp only [Scales.axial,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
    dsimp [z]
    field_simp
    <;> ring
  rw [hid,div_pow] at hE
  simpa only [eta,add_sub_cancel] using hE

end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.CapGeometry
