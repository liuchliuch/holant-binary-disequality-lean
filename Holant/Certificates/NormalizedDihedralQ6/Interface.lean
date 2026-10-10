import Holant.Certificates.NormalizedDihedralQ6.Counts
import Holant.Certificates.NormalizedDihedralQ6.ActualContraction
import Holant.Certificates.NormalizedDihedralQ6.MonomialSupport

/-! Manuscript Theorem A.11: actual cancellation-free six-to-four I/X contraction,
with exact gadget provenance and the nonsingular monomial-product obstruction. -/
namespace Holant.Certificates.NormalizedDihedralQ6
open Holant Holant.Marked Holant.Tractable
set_option backward.isDefEq.respectTransparency false

/-- Two nonsingular monomial binary factors, allowing every port permutation. -/
def TwoMonomialProduct (f : Signature Scalar 4) : Prop :=
  ∃ L R : Mat, IsMonomial L ∧ IsMonomial R ∧
    ∃ π : Equiv.Perm (Fin 4), f = Tensor.reindex π (Signature.tensor (kernelSignature L) (kernelSignature R))

theorem TwoMonomialProduct.support_card {f : Signature Scalar 4} (h : TwoMonomialProduct f) :
    coefficientSupportCard f = 4 := by
  rcases h with ⟨L,R,hL,hR,π,rfl⟩
  exact monomial_tensor_reindex_support_four hL hR π

theorem not_twoMonomialProduct_of_six_or_eight {f : Signature Scalar 4} {n : ℕ}
    (hn : n = 6 ∨ n = 8) (hc : coefficientSupportCard f = n) : ¬ TwoMonomialProduct f := by
  intro hm
  have hh := hm.support_card
  omega

/-- The complete nonmatching branch, retaining its selected original pair,
actual normalized I/X kernel, unique surviving coefficient, and exact support. -/
theorem actual_support_lowering (d₀ d₁ : Sector) (h : Signature Scalar 6)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ support d₀ d₁)
    (hn : ¬ matchingCoset (support d₀ d₁)) :
    ∃ p : Pair, ∃ hp : p.1 ≠ p.2, ∃ γ : Bool, ∃ n : ℕ,
      (n = 6 ∨ n = 8) ∧ injectiveProjection (support d₀ d₁) p γ ∧
      (projected (support d₀ d₁) p γ).card = n ∧
      Gadget.Realizes ({⟨6,h⟩} : SignatureFamily Scalar) (parityEdge γ) (contractAt h p hp γ) ∧
      coefficientSupportCard (contractAt h p hp γ) = n ∧
      ¬ TwoMonomialProduct (contractAt h p hp γ) ∧
      (∀ x, contractAt h p hp γ x ≠ 0 ↔
        x ∈ (slice (support d₀ d₁) p γ).image (externalWord p hp)) ∧
      (∀ x, x ∈ (slice (support d₀ d₁) p γ).image (externalWord p hp) →
        ∃ ab : Bool × Bool, summand h p hp γ x ab ≠ 0 ∧
          (∀ cd, summand h p hp γ x cd ≠ 0 → cd = ab) ∧
          contractAt h p hp γ x = summand h p hp γ x ab ∧
          summand h p hp γ x ab = h (joinWord p hp ab.1 ab.2 x)) := by
  classical
  have hm := nonmatching_lowering d₀ d₁ hn
  have hex : ∃ n : ℕ, (n = 6 ∨ n = 8) ∧ HasMaximum (support d₀ d₁) n := by
    rcases hm with hm | hm
    · exact ⟨6,Or.inl rfl,hm⟩
    · exact ⟨8,Or.inr rfl,hm⟩
  rcases hex with ⟨n,hn,hm⟩
  rcases hm.1 with ⟨p,γ,hp,hi,hcard⟩
  have hout : coefficientSupportCard (contractAt h p hp γ) = n := by
    simpa only [coefficientSupportCard] using (contractAt_support_card h _ hs p hp γ hi).trans hcard
  exact ⟨p,hp,γ,n,hn,hi,hcard,contraction_realizes h p hp γ,hout,
    not_twoMonomialProduct_of_six_or_eight hn hout,
    contractAt_support h _ hs p hp γ hi,cancellation_free h _ hs p hp γ hi⟩

/-- Theorem A.11. Arbitrary nonzero coefficients on an exact four-flat support
give the source's matching alternative or an actual cancellation-free lowering.
The physical gadget uses one literal h-vertex and its chosen I/X loop. -/
theorem normalized_dihedral_six_to_four (d₀ d₁ : Sector) (h : Signature Scalar 6)
    (hs : ∀ y, h y ≠ 0 ↔ y ∈ support d₀ d₁) :
    matchingCoset (support d₀ d₁) ∨
    ∃ p : Pair, ∃ hp : p.1 ≠ p.2, ∃ γ : Bool, ∃ n : ℕ,
      (n = 6 ∨ n = 8) ∧ injectiveProjection (support d₀ d₁) p γ ∧
      (projected (support d₀ d₁) p γ).card = n ∧
      Gadget.Realizes ({⟨6,h⟩} : SignatureFamily Scalar) (parityEdge γ) (contractAt h p hp γ) ∧
      coefficientSupportCard (contractAt h p hp γ) = n ∧
      ¬ TwoMonomialProduct (contractAt h p hp γ) ∧
      (∀ x, contractAt h p hp γ x ≠ 0 ↔
        x ∈ (slice (support d₀ d₁) p γ).image (externalWord p hp)) ∧
      (∀ x, x ∈ (slice (support d₀ d₁) p γ).image (externalWord p hp) →
        ∃ ab : Bool × Bool, summand h p hp γ x ab ≠ 0 ∧
          (∀ cd, summand h p hp γ x cd ≠ 0 → cd = ab) ∧
          contractAt h p hp γ x = summand h p hp γ x ab ∧
          summand h p hp γ x ab = h (joinWord p hp ab.1 ab.2 x)) := by
  classical
  by_cases hm : matchingCoset (support d₀ d₁)
  · exact Or.inl hm
  · exact Or.inr (actual_support_lowering d₀ d₁ h hs hm)

end Holant.Certificates.NormalizedDihedralQ6
