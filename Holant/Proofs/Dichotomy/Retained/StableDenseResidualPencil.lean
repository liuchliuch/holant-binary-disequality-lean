import Holant.Marked.SupportAtlas.MarkedDeck
import Holant.Proofs.Dichotomy.Retained.StableDenseParityAlgebra

/-! Dense endpoints in the actual complete root-phase deck force dependent
two-term cap pencils. The resulting coefficient identities do not classify
the dense exceptional family as tractable or hard. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualPencil
open Holant Holant.Projective Holant.Marked.SupportAtlas
open Holant.Projective.CyclicPhasePencil
open Holant.LocalDrafts.Hardness.EightVertexNonexception

/-- Both live entries in the first coordinate exclude the two axis cases of
the proved root-polygon theorem. No nonvanishing sample is assumed. -/
theorem dense_scalar_pencil {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (samples : ∀ t : ℂ, t ^ m = 1 → ScalarSample m (a + t*c) (b + t*d)) :
    ∃ α : ℂ, α ^ m = 1 ∧ b = α*a ∧ d = α*c := by
  have hs : ScalarSamples m a (-c) (-b) d := by
    intro t ht
    simpa using samples t ht
  obtain ⟨α,hr,h | h | h⟩ := relation_of_samples hm a (-c) (-b) d hs
  · refine ⟨α,hr,?_,?_⟩
    · linear_combination -h.1
    · simpa using h.2
  · exact (hc (neg_eq_zero.mp h.1)).elim
  · exact (ha h.1).elim

/-- Either parity plane of a zero-safe monomial binary gives a scalar
sample; the other parity plane is the simultaneous-zero case. -/
theorem scalarSample_of_safe {m : ℕ} (M : CMat) (safe : SafeWeighted m 1 M)
    (r : Bool) : ScalarSample m (M false r) (M true (!r)) := by
  have hI : diagonalC (1 : ℂ) = Signature.equality := by
    funext a b
    cases a <;> cases b <;> rfl
  rcases safe with hz | hs
  · left
    rw [hz]
    exact ⟨rfl,rfl⟩
  · rw [hI,Kernel.mul_equality] at hs
    cases r <;> rcases hs with hd | ho
    · exact Or.inr hd.2.2
    · exact Or.inl ⟨ho.1,ho.2.1⟩
    · exact Or.inl ⟨hd.1,hd.2.1⟩
    · exact Or.inr ho.2.2

/-- A literal ordered cap pencil has proportional coefficient columns when
both endpoints on its first residual axis survive. This uses every phase of
the actual complete group, including zero cap samples. -/
theorem dense_slice {m : ℕ} (hm : 3 ≤ m) (q : Signature ℂ 4)
    (deck : SafeDeck m 1 q) (e : Equiv.Perm (Fin 4)) (p r : Bool)
    (ha : q (fill e false p false r) ≠ 0)
    (hc : q (fill e true p false r) ≠ 0) :
    ∃ α : ℂ, α ^ m = 1 ∧
      q (fill e false p true (!r)) = α * q (fill e false p false r) ∧
      q (fill e true p true (!r)) = α * q (fill e true p false r) := by
  cases p
  · apply dense_scalar_pencil hm _ _ _ _ ha hc
    intro t ht
    have hs := scalarSample_of_safe _ (deck e false t ht) r
    simpa [weightedCard_even,binaryPencil,slice] using hs
  · obtain ⟨α,hr,hb,hd⟩ := dense_scalar_pencil hm
        (q (fill e true true false r)) (q (fill e true true true (!r)))
        (q (fill e false true false r)) (q (fill e false true true (!r))) hc ha
        (by
          intro t ht
          have hs := scalarSample_of_safe _ (deck e true t ht) r
          simpa [weightedCard_odd,binaryPencil,slice] using hs)
    exact ⟨α,hr,hd,hb⟩

theorem dense_slice_product {m : ℕ} (hm : 3 ≤ m) (q : Signature ℂ 4)
    (deck : SafeDeck m 1 q) (e : Equiv.Perm (Fin 4)) (p r : Bool)
    (ha : q (fill e false p false r) ≠ 0)
    (hc : q (fill e true p false r) ≠ 0) :
    q (fill e false p false r) * q (fill e true p true (!r)) =
      q (fill e false p true (!r)) * q (fill e true p false r) := by
  obtain ⟨α,_,hb,hd⟩ := dense_slice hm q deck e p r ha hc
  rw [hb,hd]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualPencil
end
