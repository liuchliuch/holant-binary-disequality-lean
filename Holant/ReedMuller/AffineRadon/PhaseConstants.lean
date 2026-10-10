import Holant.ReedMuller.AffineRadon.Phase

/-! The three actual orbit-sum equations used twice in source Lemma 7.19. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
variable {n : ℕ} {K : Type*} [Field K] [CharZero K]

/-- Two vanishing plus numerators make the third one exactly `2h`. -/
theorem two_zero_orbit_sums (h : BinaryVector n → K) (p q : BinaryVector n)
    (hp : ∀ x, h x+h (x+p)=0) (hq : ∀ x, h x+h (x+q)=0) (x : BinaryVector n) :
    h x+h (x+(p+q))=2*h x := by
  have H := hq (x+p)
  rw [add_assoc] at H
  linear_combination H-hp x

/-- A nonzero function cannot have all three plus numerators vanish. -/
theorem three_orbit_sums_not_all_zero (h : BinaryVector n → K) (hh : h≠0)
    (p q : BinaryVector n) :
    (∃ x, h x+h (x+p)≠0) ∨ (∃ x, h x+h (x+q)≠0) ∨
      (∃ x, h x+h (x+(p+q))≠0) := by
  classical
  by_contra H
  push_neg at H
  obtain ⟨hp,hq,hpq⟩ := H
  apply hh
  funext x
  have he := two_zero_orbit_sums h p q hp hq x
  rw [hpq] at he
  have hn : (2 : K)≠0 := by norm_num
  exact (mul_eq_zero.mp he.symm).resolve_left hn

/-- The exact coefficient identity in the manuscript. Only the three actual
orbit-sum equations on the affine support are used. -/
theorem three_constant_orbit_sums (h : BinaryVector n → K)
    (a : BinaryVector n) (U : BinaryCode n) (p q : BinaryVector n)
    (hpU : p∈U) (cp cq cpq : K)
    (hp : ∀ x, x-a∈U → h x+h (x+p)=cp)
    (hq : ∀ x, x-a∈U → h x+h (x+q)=cq)
    (hpq : ∀ x, x-a∈U → h x+h (x+(p+q))=cpq)
    (x : BinaryVector n) (hx : x-a∈U) :
    2*h x=cpq-cq+cp := by
  have hxp : x+p-a∈U := (translate_mem_iff a U p hpU x).mpr hx
  have H := hq (x+p) hxp
  rw [add_assoc] at H
  linear_combination hpq x hx+hp x hx-H

/-- Three constant orbit sums force all coefficients on the original affine
support to coincide; no phase or constancy witness is assumed for `h`. -/
theorem constant_on_support_of_three_orbit_sums (h : BinaryVector n → K)
    (a : BinaryVector n) (U : BinaryCode n) (p q : BinaryVector n)
    (hpU : p∈U) (cp cq cpq : K)
    (hp : ∀ x, x-a∈U → h x+h (x+p)=cp)
    (hq : ∀ x, x-a∈U → h x+h (x+q)=cq)
    (hpq : ∀ x, x-a∈U → h x+h (x+(p+q))=cpq) :
    ∀ x, x-a∈U → h x=(cpq-cq+cp)/2 := by
  intro x hx
  apply (eq_div_iff (by norm_num : (2 : K)≠0)).mpr
  simpa only [mul_comm] using three_constant_orbit_sums h a U p q hpU cp cq cpq hp hq hpq x hx

end
end Holant.ReedMuller.AffineRadon
