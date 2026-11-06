import Holant.Tractable.Anchor
import Holant.Tractable.Conformal.CommonBasis

/-! The endpoint-nondegenerate eight-vertex hypothesis removes the three extra
clauses of `Tract`. This proves the reduced criterion used by the STOC 2027
quaternary theorem directly from support and actual tensor decompositions.
Primality is needed by the dichotomy, but not by this stronger support lemma. -/
namespace Holant.Tractable
noncomputable section

/-- A tensor product of matching signatures with both endpoint values nonzero
cannot have a zero entry. Inverse K (or inverse KX) exposes the literal one-hot
factors, whose full-support obstruction is independent of any classification. -/
theorem not_matching_of_endpoints_and_zero {n : ℕ}
    {F : SignatureFamily AlgebraicComplex} {q : Signature AlgebraicComplex n}
    (hq : (⟨n, q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h0 : q (fun _ => false) ≠ 0) (h1 : q (fun _ => true) ≠ 0)
    (hz : ∃ x, q x = 0) :
    ¬ MatchingAlternative (familyAction sourceKBasis F) := by
  have hmem : (⟨n, sourceKBasis.action q⟩ : AnySignature AlgebraicComplex) ∈
      familyAction sourceKBasis F := ⟨⟨n, q⟩, hq, rfl⟩
  have hnonzero : sourceKBasis.action q ≠ 0 := by
    intro h
    have he := (Conformal.action_eq_zero_iff sourceKBasis q).mp h
    exact h0 (congrFun he _)
  rintro (hm | hm)
  · rcases hm _ hmem with h | h
    · exact hnonzero h
    · have ht := h.map_action sourceKBasis.inverse matchingImage_inverse_false
      change Signature.TensorClosure (fun _ g => Signature.OneHot g)
        (sourceKBasis.symm.action (sourceKBasis.action q)) at ht
      rw [InvertibleKernel.symm_action_action] at ht
      obtain ⟨x, hx⟩ := hz
      exact Signature.tensorClosure_oneHot_full_support ht h0 h1 x hx
  · rcases hm _ hmem with h | h
    · exact hnonzero h
    · have ht := h.map_action (sourceKBasis.comp bitFlipBasis).inverse
          matchingImage_inverse_true
      change Signature.TensorClosure (fun _ g => Signature.OneHot g)
        ((sourceKBasis.comp bitFlipBasis).symm.action (sourceKBasis.action q)) at ht
      simp only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
        bitFlipBasis_symm, InvertibleKernel.symm_action_action] at ht
      have h0' : bitFlipBasis.action q (fun _ => false) ≠ 0 := by
        simpa only [bitFlipBasis_action, Bool.not_false] using h1
      have h1' : bitFlipBasis.action q (fun _ => true) ≠ 0 := by
        simpa only [bitFlipBasis_action, Bool.not_true] using h0
      obtain ⟨x, hx⟩ := hz
      apply Signature.tensorClosure_oneHot_full_support ht h0' h1' (fun i => !(x i))
      simpa only [bitFlipBasis_action, Bool.not_not] using hx

/-- Three structural exclusions for an endpoint-nondegenerate eight-vertex
member, without an extra equality signature or any complexity assumption. -/
theorem quaternary_endpoint_exclusions
    {F : SignatureFamily AlgebraicComplex} {q : Signature AlgebraicComplex 4}
    (hq : (⟨4, q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (even : ∀ x, Holant.weight x % 2 = 1 → q x = 0)
    (endpoint : q (fun _ => false) * q (fun _ => true) ≠ 0) :
    ¬ OneSidedAlternative (familyAction sourceKBasis F) ∧
    ¬ SingleWeightAlternative (familyAction sourceKBasis F) ∧
    ¬ MatchingAlternative (familyAction sourceKBasis F) := by
  obtain ⟨h0, h1⟩ := mul_ne_zero_iff.mp endpoint
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hs := h.1
    rw [Conformal.kCoordinates_familyAction] at hs
    rcases hs with hs | hs
    · have hh := hs _ hq (fun _ => false) h0
      norm_num [Holant.charge, Holant.weight] at hh
    · have hh := hs _ hq (fun _ => true) h1
      norm_num [Holant.charge, Holant.weight] at hh
  · intro h
    have hs := h.1
    rw [Conformal.kCoordinates_familyAction] at hs
    obtain ⟨d, hd⟩ := hs _ hq
    have hd0 := hd.weight_of_nezero h0
    have hd1 := hd.weight_of_nezero h1
    norm_num [Holant.weight] at hd0 hd1
    omega
  · apply not_matching_of_endpoints_and_zero hq h0 h1
    exact ⟨![false, false, false, true], even _ (by decide)⟩

/-- The full seven-case criterion equals the four-case reduced criterion on
families containing an endpoint-nondegenerate eight-vertex signature. Both
sides retain the same zero/nullary preprocessing and common basis choices. -/
theorem tract_iff_tractX_of_quaternary_endpoints
    {F : SignatureFamily AlgebraicComplex} {q : Signature AlgebraicComplex 4}
    (hq : (⟨4, q⟩ : AnySignature AlgebraicComplex) ∈ F)
    (even : ∀ x, Holant.weight x % 2 = 1 → q x = 0)
    (endpoint : q (fun _ => false) * q (fun _ => true) ≠ 0) :
    Tract (familyAction sourceKBasis F) ↔ TractX (familyAction sourceKBasis F) := by
  have hnonzero : q ≠ 0 := by
    intro h
    exact (mul_ne_zero_iff.mp endpoint).1 (congrFun h _)
  have hpre : (⟨4, q⟩ : AnySignature AlgebraicComplex) ∈ preprocess F :=
    ⟨hq, by norm_num, hnonzero⟩
  have he := quaternary_endpoint_exclusions hpre even endpoint
  simp only [Tract, TractX, Conformal.preprocess_familyAction]
  apply and_congr_right
  intro _
  constructor
  · rintro (h | h | h | h | h | h | h)
    · exact (he.1 h).elim
    · exact (he.2.1 h).elim
    · exact Or.inl h
    · exact (he.2.2 h).elim
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact TractXCore.tractCore

end
end Holant.Tractable
