import Holant.Certificates.TetrahedralDeck.CardSemantics
import Holant.Certificates.TetrahedralDeck.Certificate

/-! Checked finite Gaussian identities imply exact nonzero complex matching
products with two nonsingular, actual tetrahedral binary factors. -/
namespace Holant.Certificates.TetrahedralDeck
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.MatchingProductBridge
noncomputable section

def witnessScale (s : Fin 3) (p : Fin 15) (k : Fin 12) (c : Certificate) : ℂ :=
  embed (numerator s p k c)/(4*embed (denominator c))

theorem valid_numerator_nonzero {s : Fin 3} {p : Fin 15} {k : Fin 12} {c : Certificate}
    (h : Valid s p k c) : embed (numerator s p k c) ≠ 0 := by
  intro he
  exact h.1 ((embed_zero_iff _).mp he)

theorem valid_denominator_nonzero {s : Fin 3} {p : Fin 15} {k : Fin 12} {c : Certificate}
    (h : Valid s p k c) : embed (denominator c) ≠ 0 := by
  intro he
  exact h.2.1 ((embed_zero_iff _).mp he)

theorem valid_scale_nonzero {s : Fin 3} {p : Fin 15} {k : Fin 12} {c : Certificate}
    (h : Valid s p k c) : witnessScale s p k c ≠ 0 :=
  div_ne_zero (valid_numerator_nonzero h) (mul_ne_zero (by norm_num) (valid_denominator_nonzero h))

theorem valid_exact {s : Fin 3} {p : Fin 15} {k : Fin 12} {c : Certificate}
    (h : Valid s p k c) : card s p k = witnessScale s p k c •
      matchingProduct c.1 (actualKernel c.2.1) (actualKernel c.2.2.1) := by
  funext x
  obtain ⟨j,rfl⟩ := words_surjective x
  have he := congrArg embed (h.2.2 j)
  simp only [embed_mul,embed_gCard,embed_gMatch] at he
  change card s p k (words j) = (embed (numerator s p k c)/(4*embed (denominator c)))*_
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero (by norm_num) (valid_denominator_nonzero h))).mpr
  linear_combination he

theorem valid_card_nonzero {s : Fin 3} {p : Fin 15} {k : Fin 12} {c : Certificate}
    (h : Valid s p k c) : card s p k ≠ 0 := by
  intro hz
  apply valid_numerator_nonzero h
  simp [numerator,embed_gCard,hz]

/-- Every one of the540 cases has two genuine available invertible binary factors,
with its nonzero physical scalar retained exactly. -/
theorem survivor_nonzero_matching (s : Fin 3) (p : Fin 15) (k : Fin 12) :
    card s p k ≠ 0 ∧ ∃ r : Fin 3, ∃ U V : Binary,
      groupDirection .tetrahedral (multiply U X) ∧ groupDirection .tetrahedral (multiply V X) ∧
      Matrix.det (Matrix.of U) ≠ 0 ∧ Matrix.det (Matrix.of V) ≠ 0 ∧
      ∃ c : ℂ, c ≠ 0 ∧ card s p k = c • matchingProduct r U V := by
  let c := certificate s p k
  have hc : Valid s p k c := checked_all s p k
  exact ⟨valid_card_nonzero hc,c.1,actualKernel c.2.1,actualKernel c.2.2.1,
    kernel_actual _,kernel_actual _,kernel_nonsingular _,kernel_nonsingular _,
    witnessScale s p k c,valid_scale_nonzero hc,valid_exact hc⟩

theorem survivor_in_deck (s : Fin 3) (p : Fin 15) (k : Fin 12) :
    card s p k ≠ 0 ∧ matchingCone .tetrahedral (card s p k) := by
  obtain ⟨hn,r,U,V,hU,hV,_,_,c,hc,he⟩ := survivor_nonzero_matching s p k
  exact ⟨hn,Or.inr ⟨r,U,V,hU,hV,c,hc,he⟩⟩

end
end Holant.Certificates.TetrahedralDeck
