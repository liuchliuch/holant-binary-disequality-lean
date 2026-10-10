import Holant.Proofs.Hardness.EOBinaryPlaneGram

/-! Coefficient algebra for the flat signed-cross-product residual. A failure
of common fourth powers supplies an actual row- or column-sum pair with unequal
norm squares. No conjugate signature, oracle access or hardness is asserted. -/
set_option maxRecDepth 10000
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFlat
open Holant
namespace G
export EOBinaryPlaneGram (determinant cross)
end G

theorem norm_product (z : ℂ) : z*star z=(Complex.normSq z : ℂ) := by
  simp only [Complex.star_def,Complex.mul_conj]

theorem same_norm (a b c d : ℂ) (hc : c≠0) (hx : G.cross a b c d=0) (hs : a*d+b*c=0) :
    Complex.normSq a=Complex.normSq b := by
  have hz : (a*star a-b*star b)*star c=0 := by
    calc
      _=G.cross a b c d*star a-b*star (a*d+b*c) := by
        simp only [G.cross,star_add,star_mul]
        ring
      _=0 := by rw [hx,hs]; simp
  have h := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (star_ne_zero.mpr hc))
  rw [norm_product,norm_product] at h
  exact Complex.ofReal_injective h

theorem sum_norm_identity (a b : ℂ) :
    4*Complex.normSq (a^2+b^2)=4*(Complex.normSq a-Complex.normSq b)^2+
      (Complex.normSq (a+b)-Complex.normSq (a-b))^2 := by
  simp only [pow_two,Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im]
  ring

theorem fourth_eq_of_sum_norm (a b : ℂ) (hab : Complex.normSq a=Complex.normSq b)
    (hs : Complex.normSq (a+b)=Complex.normSq (a-b)) : a^4=b^4 := by
  have hi := sum_norm_identity a b
  rw [hab,hs,sub_self,sub_self] at hi
  have hz : Complex.normSq (a^2+b^2)=0 := by nlinarith
  have h := Complex.normSq_eq_zero.mp hz
  linear_combination (a^2-b^2)*h

theorem row_sum_norm (a b c d : ℂ) (ha : a≠0) (hac : Complex.normSq a=Complex.normSq c)
    (hs : a*d+b*c=0) : Complex.normSq (c+d)=Complex.normSq (a-b) := by
  have he : a*(c+d)=c*(a-b) := by linear_combination hs
  have hn := congrArg Complex.normSq he
  simp only [map_mul,←hac] at hn
  exact mul_left_cancel₀ (Complex.normSq_pos.mpr ha).ne' hn

theorem row_sums_good (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hx : G.cross a b c d=0) (ht : G.cross a c b d=0) (hs : a*d+b*c=0)
    (hbad : a^4≠b^4) :
    a+b≠0 ∧ c+d≠0 ∧ Complex.normSq (a+b)≠Complex.normSq (c+d) := by
  have hab := same_norm a b c d hc hx hs
  have hac := same_norm a c b d hb ht (by simpa only [mul_comm b c] using hs)
  have hn := row_sum_norm a b c d ha hac hs
  refine ⟨?_,?_,?_⟩
  · intro h
    have hh : b=-a := eq_neg_of_add_eq_zero_right h
    apply hbad
    rw [hh]
    ring
  · intro h
    have hh : a-b=0 := Complex.normSq_eq_zero.mp (by rw [←hn,h]; simp)
    exact hbad (congrArg (fun z : ℂ=>z^4) (sub_eq_zero.mp hh))
  · intro h
    exact hbad (fourth_eq_of_sum_norm a b hab (h.trans hn))

/-- The two possibilities are literal ordered row sums or column sums. -/
theorem row_or_column_sums (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0)
    (hx : G.cross a b c d=0) (ht : G.cross a c b d=0) (hs : a*d+b*c=0)
    (hbad : a^4≠b^4 ∨ a^4≠c^4 ∨ a^4≠d^4) :
    (a+b≠0 ∧ c+d≠0 ∧ Complex.normSq (a+b)≠Complex.normSq (c+d)) ∨
    (a+c≠0 ∧ b+d≠0 ∧ Complex.normSq (a+c)≠Complex.normSq (b+d)) := by
  by_cases hab : a^4=b^4
  · by_cases hac : a^4=c^4
    · exfalso
      have had : a*d=-(b*c) := eq_neg_of_add_eq_zero_left hs
      have hp := congrArg (fun z : ℂ=>z^4) had
      have hn : (-(b*c))^4=b^4*c^4 := by ring
      rw [mul_pow,hn] at hp
      have he : a^4=d^4 := by
        apply mul_left_cancel₀ (pow_ne_zero 4 ha)
        calc
          a^4*a^4=b^4*c^4 := by rw [←hab,←hac]
          _=a^4*d^4 := hp.symm
      rcases hbad with hbad|hbad|hbad
      · exact hbad hab
      · exact hbad hac
      · exact hbad he
    · exact Or.inr (row_sums_good a c b d ha hc hb ht hx (by simpa only [mul_comm b c] using hs) hac)
  · exact Or.inl (row_sums_good a b c d ha hb hc hx ht hs hab)

theorem weighted_determinant (a b c d u v : ℂ) :
    G.determinant (a*u) (b*v) (c*u) (d*v)=G.determinant a b c d*u*v := by
  unfold G.determinant
  ring

theorem weighted_cross (a b c d u v : ℂ) (hx : G.cross a b c d=0) :
    G.cross (a*u) (b*v) (c*u) (d*v)=
      (a*star c)*(Complex.normSq u-Complex.normSq v : ℝ) := by
  have hh : b*star d=-(a*star c) := eq_neg_of_add_eq_zero_right hx
  calc
    _=(a*star c)*(u*star u)+(b*star d)*(v*star v) := by simp only [G.cross,star_mul]; ring
    _=(a*star c)*(Complex.normSq u-Complex.normSq v : ℝ) := by
      rw [norm_product,norm_product,hh]
      push_cast
      ring

theorem weighted_route (a b c d u v : ℂ) (ha : a≠0) (hc : c≠0)
    (hd : G.determinant a b c d≠0) (hx : G.cross a b c d=0)
    (hu : u≠0) (hv : v≠0) (hn : Complex.normSq u≠Complex.normSq v) :
    G.determinant (a*u) (b*v) (c*u) (d*v)≠0 ∧ G.cross (a*u) (b*v) (c*u) (d*v)≠0 := by
  constructor
  · rw [weighted_determinant]
    exact mul_ne_zero (mul_ne_zero hd hu) hv
  · rw [weighted_cross a b c d u v hx]
    exact mul_ne_zero (mul_ne_zero ha (star_ne_zero.mpr hc))
      (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hn))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFlat
