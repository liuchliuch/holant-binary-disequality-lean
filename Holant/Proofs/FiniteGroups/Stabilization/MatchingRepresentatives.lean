import Holant.Proofs.FiniteGroups.Stabilization.MatchingTrees


namespace Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open scoped BigOperators
noncomputable section
variable {L : Type*} [Field L]

theorem safe_binary_eq_representative (F : SignatureFamily L) (hτ : ResidualTorsion F)
    (B : Binary (K := L)) (hB : SafeBinary (actualTransfers F) B) :
    ∃ q : completeGroup F hτ, ∃ c : L, c ≠ 0 ∧ B = c • actualRepresentative F hτ q := by
  obtain ⟨C, hC, d, hd, ht⟩ := hB
  obtain ⟨q, c, hc, he⟩ := actual_binary_eq_representative F hτ C hC
  have hBC : B = d • C := by
    have hh := congrArg (fun M : Binary (K := L) => M * X) ht
    simpa only [transfer, Matrix.smul_mul, Matrix.mul_assoc, X_mul_X, Matrix.mul_one] using hh
  exact ⟨q, d * c, mul_ne_zero hd hc, by rw [hBC, he, smul_smul]⟩

def RepresentativeMatching (F : SignatureFamily L) (hτ : ResidualTorsion F)
    {n : ℕ} (f : Signature L n) : Prop :=
  ∃ (k : ℕ) (ports : (Fin k × Bool) ≃ Fin n) (label : Fin k → completeGroup F hτ)
    (c : L), c ≠ 0 ∧ f = productValue ports (fun i => actualRepresentative F hτ (label i)) c

theorem presentation_representativeMatching (F : SignatureFamily L) (hτ : ResidualTorsion F)
    {n : ℕ} (M : Presentation L (Fin n)) (hM : M.Valid (actualTransfers F)) (hc : M.scalar ≠ 0) :
    RepresentativeMatching F hτ M.tensor := by
  classical
  choose label coeff hcoeff heq using fun i => safe_binary_eq_representative F hτ (M.matrix i) (hM i)
  refine ⟨M.edges, M.ports, label, M.scalar * ∏ i, coeff i,
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hcoeff i)), ?_⟩
  funext x
  simp only [Presentation.tensor, productValue, heq, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib]
  ring

theorem matchingOrZero_iff_representatives (F : SignatureFamily L) (hτ : ResidualTorsion F)
    {n : ℕ} (f : Signature L n) :
    MatchingOrZero (actualTransfers F) f ↔ f = 0 ∨ RepresentativeMatching F hτ f := by
  constructor
  · rintro (hz | ⟨M, hM, hc, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr (presentation_representativeMatching F hτ M hM hc)
  · rintro (hz | ⟨k, p, label, c, hc, rfl⟩)
    · exact Or.inl hz
    · exact MatchingOrZero.of_product p _ c (fun i =>
        ⟨actualRepresentative F hτ (label i), actualRepresentative_actual F hτ (label i),
          1, one_ne_zero, (one_smul L _).symm⟩)

theorem RepresentativeMatching.even_arity (F : SignatureFamily L) (hτ : ResidualTorsion F)
    {n : ℕ} {f : Signature L n} (hf : RepresentativeMatching F hτ f) : Even n := by
  obtain ⟨k, p, _, _, _, _⟩ := hf
  have hp := Fintype.card_congr p
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hp
  exact ⟨k, by omega⟩

end
end Holant.LocalDrafts.FinitePGL2.Stabilization
