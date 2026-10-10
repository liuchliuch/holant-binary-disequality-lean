import Holant.Certificates.TwelveLoops.Data
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact semantic interpretation of the integer-coordinate loop tests.
Equal norms for the nonzero two-root sums are equivalent to a fourth-root
quotient; unequal norms exclude every positive finite multiplicative order. -/
namespace Holant.Certificates.TwelveLoops

def embed (z : Gaussian) : ℂ := (z.1 : ℂ)+(z.2 : ℂ)*Complex.I

theorem embed_add (z w : Gaussian) : embed (gadd z w)=embed z+embed w := by
  simp [embed,gadd]
  ring

theorem embed_mul (z w : Gaussian) : embed (gmul z w)=embed z*embed w := by
  apply Complex.ext <;> simp [embed,gmul] <;> ring

theorem embed_zero_iff (z : Gaussian) : embed z=0 ↔ z=(0,0) := by
  simp [embed,Complex.ext_iff,Prod.ext_iff]

theorem normSq_embed (z : Gaussian) : Complex.normSq (embed z)=(gnorm z : ℝ) := by
  simp [embed,gnorm,Complex.normSq_apply]

theorem fourthRoot_power (k : Fin 4) : embed (fourthRoot k)^4=1 := by
  fin_cases k <;> norm_num [fourthRoot,embed,pow_succ]

set_option maxRecDepth 10000 in
theorem equal_norm_root_multiplier : ∀ i j k l : Fin 4,
    let P := gadd (fourthRoot i) (fourthRoot j)
    let Q := gadd (fourthRoot k) (fourthRoot l)
    P ≠ (0,0) → Q ≠ (0,0) →
      (gnorm P=gnorm Q ↔ ∃ r : Fin 4, gmul (fourthRoot r) Q=P) := by decide

theorem torsion_implies_norm (P Q : Gaussian) (hQ : Q ≠ (0,0)) (n : ℕ) (hn : n≠0)
    (h : (embed P/embed Q)^n=1) : gnorm P=gnorm Q := by
  have hQ' : embed Q ≠ 0 := (not_congr (embed_zero_iff Q)).mpr hQ
  have hnorm : Complex.normSq (embed P/embed Q)=1 := by
    apply (pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg _) hn).mp
    have hh := congrArg Complex.normSq h
    simpa using hh
  rw [Complex.normSq_div,div_eq_one_iff_eq (by simpa using hQ')] at hnorm
  rw [normSq_embed,normSq_embed] at hnorm
  exact_mod_cast hnorm

theorem fourth_root_iff_equal_norm (i j k l : Fin 4)
    (hP : gadd (fourthRoot i) (fourthRoot j) ≠ (0,0))
    (hQ : gadd (fourthRoot k) (fourthRoot l) ≠ (0,0)) :
    (embed (gadd (fourthRoot i) (fourthRoot j)) /
      embed (gadd (fourthRoot k) (fourthRoot l)))^4=1 ↔
    gnorm (gadd (fourthRoot i) (fourthRoot j)) =
      gnorm (gadd (fourthRoot k) (fourthRoot l)) := by
  constructor
  · exact torsion_implies_norm _ _ hQ 4 (by decide)
  · intro heq
    obtain ⟨r,hr⟩ := (equal_norm_root_multiplier i j k l hP hQ).mp heq
    have hc := congrArg embed hr
    rw [embed_mul] at hc
    rw [← hc,mul_div_cancel_right₀ _ ((not_congr (embed_zero_iff _)).mpr hQ)]
    exact fourthRoot_power r

theorem finite_order_iff_equal_norm (i j k l : Fin 4)
    (hP : gadd (fourthRoot i) (fourthRoot j) ≠ (0,0))
    (hQ : gadd (fourthRoot k) (fourthRoot l) ≠ (0,0)) :
    (∃ n : ℕ, n≠0 ∧ (embed (gadd (fourthRoot i) (fourthRoot j)) /
      embed (gadd (fourthRoot k) (fourthRoot l)))^n=1) ↔
    gnorm (gadd (fourthRoot i) (fourthRoot j)) =
      gnorm (gadd (fourthRoot k) (fourthRoot l)) := by
  constructor
  · rintro ⟨n,hn,h⟩
    exact torsion_implies_norm _ _ hQ n hn h
  · intro h
    exact ⟨4,by decide,(fourth_root_iff_equal_norm i j k l hP hQ).mpr h⟩

end Holant.Certificates.TwelveLoops
