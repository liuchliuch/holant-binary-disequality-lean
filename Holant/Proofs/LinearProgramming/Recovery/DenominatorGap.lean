import Holant.Proofs.LinearProgramming.Interface
import Holant.Algebraic.RationalHeight

set_option autoImplicit false

/-! Exact rational separation, independent of LP optimization and recovery.
This module makes no algorithmic claim: it supplies the uniqueness theorem
used to identify the scalar returned by the physical extractor. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery.Denominator

private theorem integer_abs_gap (c : ℤ) (hc : c ≠ 0) : (1 : ℚ) ≤ |(c : ℚ)| := by
  have hi : (1 : ℤ) ≤ |c| := by
    have hn := abs_nonneg c
    have he : |c| ≠ 0 := abs_ne_zero.mpr hc
    omega
  exact_mod_cast hi

theorem box_numerator (q : ℚ) (hq : 0≤q ∧ q≤1) : q.num.natAbs≤q.den := by
  have hd : (0:ℚ)<q.den := by exact_mod_cast q.den_pos
  have hn : 0≤q.num := Rat.num_nonneg.mpr hq.1
  have hle : (q.num:ℚ)≤q.den := by
    have h : (q.num:ℚ)/(q.den:ℚ)≤1 := by simpa only [Rat.num_div_den] using hq.2
    simpa using (div_le_iff₀ hd).mp h
  have hle' : q.num≤(q.den:ℤ) := by exact_mod_cast hle
  exact_mod_cast (show (q.num.natAbs:ℤ)≤(q.den:ℤ) by simpa [Int.natCast_natAbs,abs_of_nonneg hn] using hle')

theorem distinct_gap (D : ℕ) (hD : 0<D) (a b : ℚ)
    (ha : a.den≤D) (hb : b.den≤D) (hne : a≠b) : 1/(D:ℚ)^2≤|a-b| := by
  let c : ℤ := a.num*(b.den:ℤ)-b.num*(a.den:ℤ)
  have ha0 : (a.den:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt a.den_pos)
  have hb0 : (b.den:ℚ)≠0 := by exact_mod_cast (Nat.ne_of_gt b.den_pos)
  have hd : (0:ℚ)<(a.den:ℚ)*b.den := mul_pos (by exact_mod_cast a.den_pos) (by exact_mod_cast b.den_pos)
  have he : a-b=(c:ℚ)/((a.den:ℚ)*b.den) := by
    calc
      a-b=(a.num:ℚ)/a.den-(b.num:ℚ)/b.den := by rw [Rat.num_div_den,Rat.num_div_den]
      _=(c:ℚ)/((a.den:ℚ)*b.den) := by
        dsimp [c]
        push_cast
        field_simp [ha0,hb0] <;> ring
  have hc : c≠0 := by
    intro hz
    apply hne
    apply sub_eq_zero.mp
    rw [he,hz,Int.cast_zero,zero_div]
  have hg := integer_abs_gap c hc
  have habs : |a-b| * ((a.den:ℚ)*b.den)=|(c:ℚ)| := by
    rw [he,abs_div,abs_of_pos hd]
    exact div_mul_cancel₀ _ (ne_of_gt hd)
  have hprod : (a.den:ℚ)*b.den≤(D:ℚ)^2 := by
    have ha' : (a.den:ℚ)≤D := by exact_mod_cast ha
    have hb' : (b.den:ℚ)≤D := by exact_mod_cast hb
    simpa [pow_two] using mul_le_mul ha' hb' (Nat.cast_nonneg b.den) (Nat.cast_nonneg D)
  have hm : 1≤|a-b| * (D:ℚ)^2 := by
    calc
      1≤|a-b| * ((a.den:ℚ)*b.den) := by rw [habs]; exact hg
      _≤|a-b| * (D:ℚ)^2 := mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
  have hD' : (0:ℚ)<D := by exact_mod_cast hD
  exact (div_le_iff₀ (sq_pos_of_pos hD')).mpr hm

theorem interval_unique (D : ℕ) (hD : 0<D) (l u a b : ℚ)
    (ha : l≤a ∧ a≤u) (hb : l≤b ∧ b≤u)
    (hda : a.den≤D) (hdb : b.den≤D) (hw : u-l<1/(D:ℚ)^2) : a=b := by
  by_contra hn
  have hg := distinct_gap D hD a b hda hdb hn
  have he : |a-b|≤u-l := abs_le.mpr ⟨by linarith,by linarith⟩
  exact (not_le_of_gt hw) (hg.trans he)

end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery.Denominator
