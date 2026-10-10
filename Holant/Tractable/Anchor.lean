import Holant.Tractable.Criteria
import Holant.Tractable.Anchor.MatrixActions

/-!
# Binary anchors remove three alternatives

Authoritative manuscript Lemma `lem:tract-X-anchor` (Lemma 2.12).
The matching obstruction is established from actual disjoint tensor factors;
no tensor-primality characterization or complexity theorem is assumed.
-/

namespace Holant.Tractable
noncomputable section

/-- A binary supported exactly on its two nonzero endpoints. -/
def BinaryEndpointSupport (f : Signature AlgebraicComplex 2) : Prop :=
  f (fun _ => false) ≠ 0 ∧ f (fun _ => true) ≠ 0 ∧
  f ![false, true] = 0 ∧ f ![true, false] = 0

theorem BinaryEndpointSupport.not_one_sided {G : SignatureFamily AlgebraicComplex}
    {g : Signature AlgebraicComplex 2} (h : BinaryEndpointSupport g)
    (hg : (⟨2, g⟩ : AnySignature AlgebraicComplex) ∈ G) : ¬ CommonOneSided G := by
  rintro (hp | hn)
  · have hc := hp ⟨2, g⟩ hg (fun _ => false) h.1
    norm_num [Holant.charge, Holant.weight] at hc
  · have hc := hn ⟨2, g⟩ hg (fun _ => true) h.2.1
    norm_num [Holant.charge, Holant.weight] at hc

theorem BinaryEndpointSupport.not_single_layer {g : Signature AlgebraicComplex 2}
    (h : BinaryEndpointSupport g) (d : ℕ) : ¬ Signature.SingleLayer g d := by
  intro hl
  have h0 := hl.weight_of_nezero h.1
  have h1 := hl.weight_of_nezero h.2.1
  norm_num [Holant.weight] at h0 h1
  omega

theorem BinaryEndpointSupport.flip {g : Signature AlgebraicComplex 2}
    (h : BinaryEndpointSupport g) : BinaryEndpointSupport (bitFlipBasis.action g) := by
  have h01 : (fun j : Fin 2 => !(![false, true] j)) = ![true, false] := by
    funext j
    fin_cases j <;> rfl
  have h10 : (fun j : Fin 2 => !(![true, false] j)) = ![false, true] := by
    funext j
    fin_cases j <;> rfl
  simpa only [BinaryEndpointSupport, bitFlipBasis_action, Bool.not_false,
    Bool.not_true, h01, h10] using ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem BinaryEndpointSupport.not_matching_tensor {g : Signature AlgebraicComplex 2}
    (h : BinaryEndpointSupport g) :
    ¬ Signature.TensorClosure (fun _ f => Signature.OneHot f) g :=
  Signature.not_tensorClosure_oneHot_of_binary_endpoints g h.1 h.2.1 h.2.2.1

/-- The inverse transform of each literal K-image factor recovers its M witness. -/
theorem matchingImage_inverse_false (n : ℕ) (g : Signature AlgebraicComplex n)
    (h : matchingImage false n g) :
    Signature.OneHot (sourceKBasis.symm.action g) := by
  obtain ⟨f, hf, rfl⟩ := h
  change Signature.OneHot (sourceKBasis.symm.action (sourceKBasis.action f))
  simpa [InvertibleKernel.symm_action_action, Signature.OneHot, AtMostOneSupport,
    Holant.weight, Holant.Tractable.weight] using hf

/-- The opposite orientation uses the inverse of KX, namely XK⁻¹, at every port. -/
theorem matchingImage_inverse_true (n : ℕ) (g : Signature AlgebraicComplex n)
    (h : matchingImage true n g) :
    Signature.OneHot ((sourceKBasis.comp bitFlipBasis).symm.action g) := by
  obtain ⟨f, hf, rfl⟩ := h
  change Signature.OneHot ((sourceKBasis.comp bitFlipBasis).symm.action
    ((sourceKBasis.comp bitFlipBasis).action f))
  simpa [InvertibleKernel.symm_action_action, Signature.OneHot, AtMostOneSupport,
    Holant.weight, Holant.Tractable.weight] using hf

theorem not_matching_false_of_inverse_endpoints {f : Signature AlgebraicComplex 2}
    (h : BinaryEndpointSupport (sourceKBasis.symm.action f)) :
    ¬ SourceTensorClosure (matchingImage false) f := by
  rintro (hz | ht)
  · have hh := h.1
    simp [hz, InvertibleKernel.action] at hh
  · apply h.not_matching_tensor
    exact ht.map_action sourceKBasis.inverse matchingImage_inverse_false

theorem not_matching_true_of_inverse_endpoints {f : Signature AlgebraicComplex 2}
    (h : BinaryEndpointSupport (sourceKBasis.symm.action f)) :
    ¬ SourceTensorClosure (matchingImage true) f := by
  rintro (hz | ht)
  · have hh := h.1
    simp [hz, InvertibleKernel.action] at hh
  · apply h.flip.not_matching_tensor
    have hh := ht.map_action (sourceKBasis.comp bitFlipBasis).inverse matchingImage_inverse_true
    change Signature.TensorClosure (fun _ g => Signature.OneHot g)
      ((sourceKBasis.comp bitFlipBasis).symm.action f) at hh
    simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
      bitFlipBasis_symm] using hh

/-- The concrete three obstructions are independent of the remaining signatures. -/
theorem binary_endpoint_exclusions {F : SignatureFamily AlgebraicComplex}
    {f : Signature AlgebraicComplex 2}
    (hf : (⟨2, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h : BinaryEndpointSupport (sourceKBasis.symm.action f)) :
    ¬ OneSidedAlternative F ∧ ¬ SingleWeightAlternative F ∧ ¬ MatchingAlternative F := by
  have hmem : (⟨2, sourceKBasis.symm.action f⟩ : AnySignature AlgebraicComplex) ∈
      kCoordinates F := ⟨⟨2, f⟩, hf, rfl⟩
  refine ⟨fun hc => h.not_one_sided hmem hc.1, ?_, ?_⟩
  · intro hc
    obtain ⟨d, hd⟩ := hc.1 _ hmem
    exact h.not_single_layer d hd
  · rintro (hc | hc)
    · exact not_matching_false_of_inverse_endpoints h (hc _ hf)
    · exact not_matching_true_of_inverse_endpoints h (hc _ hf)

/-- The seven alternatives reduce to exactly the retained four, by actual support
and tensor-product obstructions at the specified binary member. -/
theorem tractCore_iff_tractXCore_of_binary_endpoints {F : SignatureFamily AlgebraicComplex}
    {f : Signature AlgebraicComplex 2}
    (hf : (⟨2, f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h : BinaryEndpointSupport (sourceKBasis.symm.action f)) :
    TractCore F ↔ TractXCore F := by
  have he := binary_endpoint_exclusions hf h
  constructor
  · rintro (hc | hc | hc | hc | hc | hc | hc)
    · exact (he.1 hc).elim
    · exact (he.2.1 hc).elim
    · exact Or.inl hc
    · exact (he.2.2 hc).elim
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hc))
  · exact TractXCore.tractCore

/-- The exact K⁻¹X = -iZ identity supplies both nonzero endpoints. -/
theorem inverse_xAnchor_endpoints : BinaryEndpointSupport (sourceKBasis.symm.action xAnchor) := by
  rw [sourceKBasis_symm_action_xAnchor]
  have hi : imaginaryUnit ≠ 0 := by
    intro h
    have hh := imaginaryUnit_sq
    rw [h] at hh
    norm_num at hh
  simp [BinaryEndpointSupport, kernelSignature, diagonalKernel, hi]

/-- The exact K⁻¹Z = I identity supplies both nonzero endpoints. -/
theorem inverse_zAnchor_endpoints : BinaryEndpointSupport (sourceKBasis.symm.action zAnchor) := by
  rw [sourceKBasis_symm_action_zAnchor]
  simp [BinaryEndpointSupport, kernelSignature, Signature.equality]

@[simp] theorem xAnchor_ne_zero : xAnchor ≠ 0 := by
  intro hz
  have h := congrFun hz ![false, true]
  norm_num [xAnchor, kernelSignature, Signature.disequality] at h

@[simp] theorem zAnchor_ne_zero : zAnchor ≠ 0 := by
  intro hz
  have h := congrFun hz (fun _ => false)
  norm_num [zAnchor, kernelSignature, diagonalKernel] at h

/-- Lemma 2.12, literal-X version. This includes arbitrary supplied zero and
nullary signatures because the criterion applies the prescribed preprocessing. -/
theorem tract_iff_tractX_of_xAnchor_mem {F : SignatureFamily AlgebraicComplex}
    (hX : (⟨2, xAnchor⟩ : AnySignature AlgebraicComplex) ∈ F) : Tract F ↔ TractX F := by
  have hm : (⟨2, xAnchor⟩ : AnySignature AlgebraicComplex) ∈ preprocess F :=
    ⟨hX, by decide, xAnchor_ne_zero⟩
  exact and_congr_right (fun _ => tractCore_iff_tractXCore_of_binary_endpoints hm inverse_xAnchor_endpoints)

/-- Lemma 2.12, literal-Z version, for the coordinate images in the main theorems. -/
theorem tract_iff_tractX_of_zAnchor_mem {F : SignatureFamily AlgebraicComplex}
    (hZ : (⟨2, zAnchor⟩ : AnySignature AlgebraicComplex) ∈ F) : Tract F ↔ TractX F := by
  have hm : (⟨2, zAnchor⟩ : AnySignature AlgebraicComplex) ∈ preprocess F :=
    ⟨hZ, by decide, zAnchor_ne_zero⟩
  exact and_congr_right (fun _ => tractCore_iff_tractXCore_of_binary_endpoints hm inverse_zAnchor_endpoints)

/-- The source statement for a finite preprocessed family with either anchor. -/
theorem binary_anchor {F : SignatureFamily AlgebraicComplex}
    (_hfinite : F.Finite) (_hpreprocessed : Preprocessed F)
    (hanchor : (⟨2, xAnchor⟩ : AnySignature AlgebraicComplex) ∈ F ∨
      (⟨2, zAnchor⟩ : AnySignature AlgebraicComplex) ∈ F) : Tract F ↔ TractX F := by
  rcases hanchor with hX | hZ
  · exact tract_iff_tractX_of_xAnchor_mem hX
  · exact tract_iff_tractX_of_zAnchor_mem hZ

end
end Holant.Tractable
