import Holant.Proofs.Hardness.EightVertexGaugeTwoRowAlgebra
import Holant.Marked.SupportAtlas.MarkedDeck

/-! A physical two-row test of the weighted-even residual. Unequal fourth
powers make the crossed output dense and violate its complementary products.
Consequently that output cannot have a safe complete monomial phase deck.
This is an explicit new-deck obstruction, not unconditional hardness: applying
the current refinement to a new occurrence still requires its actual access
and may return an affine/product row before reaching the dense alternative. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowPencil
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open EightVertexGaugeTwoRowAlgebra
open Holant.Marked.SupportAtlas
variable {K : Type} [Field K]

export EightVertexGaugeSectorAlgebra (self_crossed_live)

theorem self_crossed_not_products (a : K) (u : Fin 4 → K)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0) (different : u 2 ^ 4 ≠ u 3 ^ 4) :
    ¬ StableDenseResidualGaugeCore.Products (output a a u u true) := by
  intro hp
  have hs : u 2 ^ 2-u 3 ^ 2 ≠ 0 := by
    intro hz
    apply different
    have h := sub_eq_zero.mp hz
    calc u 2 ^ 4 = (u 2 ^ 2)^2 := by ring
         _ = (u 3 ^ 2)^2 := by rw [h]
         _ = u 3 ^ 4 := by ring
  have hp' := (products_iff a a u u true ha ha hu hu).mp hp
  have hf := self_crossed_factor u
  rw [hp',sub_self] at hf
  exact (neg_ne_zero.mpr (pow_ne_zero 2 hs)) hf.symm

/-- Actual two-copy output: every even word survives, and a complementary
product equation fails. The theorem deliberately has no hardness conclusion. -/
theorem self_crossed_escape [CharZero K] (a : K) (u : Fin 4 → K)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0) (different : u 2 ^ 4 ≠ u 3 ^ 4) :
    (∀ x, output a a u u true x ≠ 0 ↔ parity x = false) ∧
      ¬ StableDenseResidualGaugeCore.Products (output a a u u true) := by
  have live := self_crossed_live u hu different
  exact ⟨output_full a a u u true ha ha hu hu live.1 live.2,
    self_crossed_not_products a u ha hu different⟩

private theorem diagonal_sample {m : ℕ} (M : Holant.Marked.SupportAtlas.CMat)
    (safe : SafeWeighted m 1 M) :
    Holant.Projective.CyclicPhasePencil.ScalarSample m (M false false) (M true true) := by
  have hI : diagonalC (1 : ℂ) = Signature.equality := by
    funext a b
    cases a <;> cases b <;> rfl
  rcases safe with hz | hs
  · exact Or.inl (by rw [hz]; exact ⟨rfl,rfl⟩)
  · rw [hI,Kernel.mul_equality] at hs
    rcases hs with hd | ho
    · exact Or.inr hd.2.2
    · exact Or.inl ⟨ho.1,ho.2.1⟩

private theorem pencil_product {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (samples : ∀ t : ℂ, t ^ m = 1 →
      Holant.Projective.CyclicPhasePencil.ScalarSample m (a+t*c) (b+t*d)) : a*d=b*c := by
  have hs : Holant.Projective.CyclicPhasePencil.ScalarSamples m a (-c) (-b) d := by
    intro t ht
    simpa using samples t ht
  obtain ⟨α,_,h | h | h⟩ :=
    Holant.Projective.CyclicPhasePencil.relation_of_samples hm a (-c) (-b) d hs
  · have hb : b = α*a := by linear_combination -h.1
    have hd : d = α*c := by simpa using h.2
    rw [hb,hd]
    ring
  · exact (hc (neg_eq_zero.mp h.1)).elim
  · exact (ha h.1).elim

/-- Only the actual 02-deleted even pencil is needed for this product.
The finite root-polygon relation supplies proportionality, including zeros. -/
private theorem safe_cross_product {m : ℕ} (hm : 3 ≤ m) (q : Signature ℂ 4)
    (deck : SafeDeck m 1 q) (ha : q ![false,false,false,false] ≠ 0)
    (hc : q ![true,false,true,false] ≠ 0) :
    q ![false,false,false,false] * q ![true,true,true,true] =
      q ![false,true,false,true] * q ![true,false,true,false] := by
  apply pencil_product hm _ _ _ _ ha hc
  intro t ht
  have hs := diagonal_sample _ (deck (Equiv.swap (1 : Fin 4) 2) false t ht)
  have hj (a b u v : Bool) : join (Equiv.swap (1 : Fin 4) 2) a b u v = ![a,u,b,v] := by
    funext i
    fin_cases i <;> simp [join,Equiv.swap_apply_def]
  simpa [weightedCard_even,Holant.Projective.binaryPencil,slice,fill_eq_join,hj] using hs

/-- The existing finite-pencil theorem applies to the NEW row only when
its own complete deck is safe. It then forces equal sector squares. -/
theorem safe_output_factors {m : ℕ} (hm : 3 ≤ m) (a b : ℂ)
    (u v : Fin 4 → ℂ) (cross : Bool)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (hE : evenFactor u v ≠ 0) (hO : oddFactor u v cross ≠ 0)
    (deck : SafeDeck m 1 (output a b u v cross)) :
    evenFactor u v ^ 2 = oddFactor u v cross ^ 2 := by
  have full := output_full a b u v cross ha hb hu hv hE hO
  have hp := safe_cross_product hm (output a b u v cross) deck
    ((full _).mpr (by decide)) ((full _).mpr (by decide))
  have hz := defect a b u v cross
  change (entries (output a b u v cross)).a*(entries (output a b u v cross)).x =
    (entries (output a b u v cross)).c*(entries (output a b u v cross)).z at hp
  rw [hp,sub_self] at hz
  have hc : (a*b)^2*u 0*u 1*v 0*v 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (mul_ne_zero ha hb)) (hu 0)) (hu 1)) (hv 0)) (hv 1)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz.symm).resolve_left hc)

theorem self_crossed_not_safe {m : ℕ} (hm : 3 ≤ m) (a : ℂ) (u : Fin 4 → ℂ)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0) (different : u 2 ^ 4 ≠ u 3 ^ 4) :
    ¬ SafeDeck m 1 (output a a u u true) := by
  intro deck
  have live := self_crossed_live u hu different
  have hf := safe_output_factors hm a a u u true ha ha hu hu live.1 live.2 deck
  exact self_crossed_not_products a u ha hu different
    ((products_iff a a u u true ha ha hu hu).mpr hf)

/-- At least one actual phase sample of the new complete deck must fail.
Zero samples were included in the safe predicate, so this witness is nonzero. -/
theorem self_crossed_unsafe_sample {m : ℕ} (hm : 3 ≤ m) (a : ℂ) (u : Fin 4 → ℂ)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0) (different : u 2 ^ 4 ≠ u 3 ^ 4) :
    ∃ (e : Equiv.Perm (Fin 4)) (p : Bool) (t : ℂ), t ^ m = 1 ∧
      ¬ SafeWeighted m 1 (weightedCard 1 (output a a u u true) e p t) := by
  have h := self_crossed_not_safe hm a u ha hu different
  unfold SafeDeck at h
  push Not at h
  exact h

theorem self_crossed_safe_fourth {m : ℕ} (hm : 3 ≤ m) (a : ℂ) (u : Fin 4 → ℂ)
    (ha : a ≠ 0) (hu : ∀ i, u i ≠ 0)
    (deck : SafeDeck m 1 (output a a u u true)) : u 2 ^ 4 = u 3 ^ 4 := by
  by_contra different
  exact self_crossed_not_safe hm a u ha hu different deck

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowPencil
end
