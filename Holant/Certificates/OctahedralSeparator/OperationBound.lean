import Holant.Certificates.OctahedralSeparator.PublicClauses

namespace Holant.Certificates.OctahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem BoundedNativeRealization.realizes {n : ℕ} {f : Form} {h : Signature ℂ 6}
    {K : Native.Binary} {t : Signature ℂ n} (ht : BoundedNativeRealization f h K t) :
    Gadget.Realizes (markedResources f h) .disequality t := by
  obtain ⟨N,initial,hden,hi,hv,he,ha,hb⟩ := ht
  have hx := Gadget.realizes_network N (markedResources f h) .disequality hv he
  rwa [hden] at hx

def BoundedResolved (f : Form) (h : Signature ℂ 6) (K : Native.Binary) : Prop :=
  (∃ t : Signature ℂ 4, BoundedNativeRealization f h K t ∧
    TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧ ∀ r : Fin 3, (flatten r t).rank=2) ∨
  (∃ c : ℂ, c ≠ 0 ∧ BoundedNativeRealization f h K (c • complexEq4)) ∨
  ∃ B : Native.Binary, BoundedNativeRealization f h K (Native.binarySignature B) ∧
    Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction f (nativeTransfer B)

theorem BoundedResolved.resolved {f : Form} {h : Signature ℂ 6} {K : Native.Binary}
    (hx : BoundedResolved f h K) : Resolved f h := by
  rcases hx with ⟨t,ht,he,hr⟩ | ⟨c,hc,ht⟩ | ⟨B,hB,hd,ho⟩
  · exact Or.inl ⟨t,ht.realizes,he,hr⟩
  · exact Or.inr (Or.inl ⟨c,hc,ht.realizes⟩)
  · exact Or.inr (Or.inr ⟨B,hB.realizes,hd,ho⟩)

theorem bounded_resolved_row (j : Fin 48) (h : Signature ℂ 6) (p : Equiv.Perm (Fin 6)) (K : Native.Binary)
    (hK : Direction (rowForm j) (Matrix.of K))
    (hcard : Signature.contract K (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j))) : BoundedResolved (rowForm j) h K := by
  by_cases ho : outsideRow j
  · exact Or.inr (Or.inr ⟨complexMatrix (outsideValues j),bounded_outside_network j ho h p K hK hcard,
      outside_nonsingular j ho,outside_transfer_not_direction j ho⟩)
  · by_cases he : j=34
    · subst j
      refine Or.inr (Or.inl ⟨embed (coeff (3/8) (1/4) 0 0),equality_output_scale_nonzero,?_⟩)
      rw [← equality_output]
      exact bounded_endpoint_network 34 ho h p K hK hcard
    · exact Or.inl ⟨complexTensor (endpointOutput j),bounded_endpoint_network j ho h p K hK hcard,
        endpoint_eightVertex j ho,endpoint_rank_two j ho⟩

/-- The actual initial displayed kernel is distinguished in the network. Every
normalized full-frame source has one of the stated exits using at most four
further current-group binaries and exactly one copy of the original ancestor. -/
theorem uniform_octahedral_operation_bound (f : Form) (frame : Fin 4) (order : Fin 6)
    (h : Signature ℂ 6) (hN : NormalizedCardMap f (fullImages frame order) h) :
    BoundedResolved f h (complexMatrix (theta f firstKernel)) := by
  let j := regularRow f (frames frame (permutations order 0))
  have hcard : Signature.contract (complexMatrix (theta f firstKernel))
      (Tensor.reindex (Equiv.refl _) h)=complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    simpa only [j,regularRow_form,regularRow_base,Tensor.reindex_refl] using normalized_first_card f frame order h hN
  have hK : Direction (rowForm j) (Matrix.of (complexMatrix (theta f firstKernel))) := by
    change Direction (rowForm j) (complexMatrix (theta f firstKernel))
    simpa only [j,regularRow_form] using firstKernel_available f
  simpa only [j,regularRow_form] using bounded_resolved_row j h (Equiv.refl _) _ hK hcard

theorem deficient_mixed_operation_bound (f : Fin 2) (order : Fin 6) :
    ∃ B : Native.Binary,
      BoundedNativeRealization (mixedForm f) (complexTensor (deficientAncestor (mixedForm f) order))
        (complexMatrix (q 0)) (Native.binarySignature B) ∧
      Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction (mixedForm f) (nativeTransfer B) := by
  let j := deficientRow f order
  let h := complexTensor (deficientAncestor (mixedForm f) order)
  let p := (TetrahedralDeck.portOrder 1).symm
  have hcard : Signature.contract (complexMatrix (q 0)) (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    rw [← complexTensor_reindex,← complexTensor_contract,deficient_card_exact]
    simp only [j,deficientRow_form,deficientRow_base]
  have hK : Direction (rowForm j) (Matrix.of (complexMatrix (q 0))) := direction_identity _
  refine ⟨complexMatrix (outsideValues j),?_,outside_nonsingular j (deficientRow_outside f order),?_⟩
  · simpa only [j,deficientRow_form] using
      bounded_outside_network j (deficientRow_outside f order) h p _ hK hcard
  · simpa only [j,deficientRow_form] using outside_transfer_not_direction j (deficientRow_outside f order)

end
end Holant.Certificates.OctahedralSeparator
