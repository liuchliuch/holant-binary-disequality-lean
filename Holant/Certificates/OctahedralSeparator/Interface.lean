import Holant.Certificates.OctahedralSeparator.PhysicalOutputs
import Holant.Certificates.OctahedralSeparator.ExitSemantics
import Holant.Certificates.OctahedralSeparator.CardMap
import Holant.Certificates.OctahedralSeparator.CaseIndex
import Holant.Certificates.OctahedralSeparator.SourceErrata
import Holant.Certificates.OctahedralSeparator.GroupMatrixInverses
import Holant.Certificates.OctahedralSeparator.DirectionMultiplicities

/-! Current Lemma9.12 and PropositionA.16: actual current-form kernels,
literal native-X networks, and all full-rank and deficient source cases.
The two false preliminary plus-sign marked identities are separately recorded
in SourceErrata; this result uses the source's literal matrices. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def Resolved (f : Form) (h : Signature ℂ 6) : Prop :=
  (∃ q : Signature ℂ 4,
    Gadget.Realizes (markedResources f h) .disequality q ∧
    TetrahedralOrientation.EndpointNondegenerateEightVertex q ∧
    ∀ r : Fin 3, (flatten r q).rank=2) ∨
  (∃ c : ℂ, c ≠ 0 ∧ Gadget.Realizes (markedResources f h) .disequality (c • complexEq4)) ∨
  ∃ B : Native.Binary,
    Gadget.Realizes (markedResources f h) .disequality (Native.binarySignature B) ∧
    Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction f (nativeTransfer B)

theorem resolved_row (j : Fin 48) (h : Signature ℂ 6) (p : Equiv.Perm (Fin 6)) (K : Native.Binary)
    (hK : Direction (rowForm j) (Matrix.of K))
    (hcard : Signature.contract K (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j))) : Resolved (rowForm j) h := by
  by_cases ho : outsideRow j
  · exact Or.inr (Or.inr ⟨complexMatrix (outsideValues j),outside_realizes j ho h p K hK hcard,
      outside_nonsingular j ho,outside_transfer_not_direction j ho⟩)
  · by_cases he : j=34
    · subst j
      refine Or.inr (Or.inl ⟨embed (coeff (3/8) (1/4) 0 0),equality_output_scale_nonzero,?_⟩)
      rw [← equality_output]
      exact endpoint_realizes 34 ho h p K hK hcard
    · exact Or.inl ⟨complexTensor (endpointOutput j),endpoint_realizes j ho h p K hK hcard,
        endpoint_eightVertex j ho,endpoint_rank_two j ho⟩

/-- Lemma9.12 for an arbitrary actual six-port signature with the normalized
source card map. The source hypothesis supplies basis cards, not a gadget exit. -/
theorem uniform_octahedral_full_rank_exits (f : Form) (frame : Fin 4) (order : Fin 6)
    (h : Signature ℂ 6) (hN : NormalizedCardMap f (fullImages frame order) h) : Resolved f h := by
  let r := frames frame (permutations order 0)
  let j := regularRow f r
  have hcard : Signature.contract (complexMatrix (theta f firstKernel))
      (Tensor.reindex (Equiv.refl _) h)=complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    simpa only [j,regularRow_form,regularRow_base,Tensor.reindex_refl] using
      normalized_first_card f frame order h hN
  have hK : Direction (rowForm j) (Matrix.of (complexMatrix (theta f firstKernel))) := by
    change Direction (rowForm j) (complexMatrix (theta f firstKernel))
    simpa only [j,regularRow_form] using firstKernel_available f
  have hx := resolved_row j h (Equiv.refl _) (complexMatrix (theta f firstKernel)) hK hcard
  simpa only [j,regularRow_form] using hx

theorem normalized_endpoint_exit (f : Form) (frame : Fin 4) (order : Fin 6)
    (h : Signature ℂ 6) (hN : NormalizedCardMap f (fullImages frame order) h)
    (ho : ¬outsideRow (regularRow f (frames frame (permutations order 0)))) :
    ∃ q : Signature ℂ 4, Gadget.Realizes (markedResources f h) .disequality q ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex q ∧ ∀ r : Fin 3, (flatten r q).rank=2 := by
  let j := regularRow f (frames frame (permutations order 0))
  have hcard : Signature.contract (complexMatrix (theta f firstKernel))
      (Tensor.reindex (Equiv.refl _) h)=complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    simpa only [j,regularRow_form,regularRow_base,Tensor.reindex_refl] using
      normalized_first_card f frame order h hN
  have hK : Direction (rowForm j) (Matrix.of (complexMatrix (theta f firstKernel))) := by
    change Direction (rowForm j) (complexMatrix (theta f firstKernel))
    simpa only [j,regularRow_form] using firstKernel_available f
  refine ⟨complexTensor (endpointOutput j),?_,endpoint_eightVertex j ho,endpoint_rank_two j ho⟩
  simpa only [j,regularRow_form] using endpoint_realizes j ho h (Equiv.refl _) _ hK hcard

theorem standard_prime_rows : ∀ f : Fin 2, ∀ r : Fin 9,
    ¬outsideRow (regularRow (Fin.castAdd 2 f) r) := by decide

/-- In both unmixed forms every one of the24 ordered maps takes the stronger
endpoint eight-vertex exit. -/
theorem standard_prime_eight_vertex (f : Fin 2) (frame : Fin 4) (order : Fin 6)
    (h : Signature ℂ 6) (hN : NormalizedCardMap (Fin.castAdd 2 f) (fullImages frame order) h) :
    ∃ q : Signature ℂ 4, Gadget.Realizes (markedResources (Fin.castAdd 2 f) h) .disequality q ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex q ∧ ∀ r : Fin 3, (flatten r q).rank=2 :=
  normalized_endpoint_exit _ frame order h hN (standard_prime_rows f _)

theorem full_reconstructed_exits (f : Form) (frame : Fin 4) (order : Fin 6) :
    Resolved f (complexTensor (fullAncestor f frame order)) :=
  uniform_octahedral_full_rank_exits f frame order _ (reconstructed_normalized f _)

theorem deficientRow_outside : ∀ f : Fin 2, ∀ p : Fin 6, outsideRow (deficientRow f p) := by decide

/-- All twelve deficient mixed cases contract original ports1/3 using literal I,
then two actual current-form corrections and the displayed final kernel. -/
theorem deficient_mixed_exits (f : Fin 2) (order : Fin 6) :
    ∃ B : Native.Binary,
      Gadget.Realizes (markedResources (mixedForm f)
        (complexTensor (deficientAncestor (mixedForm f) order))) .disequality (Native.binarySignature B) ∧
      Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction (mixedForm f) (nativeTransfer B) := by
  let j := deficientRow f order
  let h := complexTensor (deficientAncestor (mixedForm f) order)
  let p := (TetrahedralDeck.portOrder 1).symm
  have hcard : Signature.contract (complexMatrix (q 0)) (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    rw [← complexTensor_reindex,← complexTensor_contract,deficient_card_exact]
    simp only [j,deficientRow_form,deficientRow_base]
  have hK : Direction (rowForm j) (Matrix.of (complexMatrix (q 0))) := by
    exact direction_identity _
  have hr := outside_realizes j (deficientRow_outside f order) h p (complexMatrix (q 0)) hK hcard
  refine ⟨complexMatrix (outsideValues j),?_,outside_nonsingular j (deficientRow_outside f order),?_⟩
  · simpa only [j,deficientRow_form] using hr
  · simpa only [j,deficientRow_form] using outside_transfer_not_direction j (deficientRow_outside f order)

/-- PropositionA.16: the stronger endpoint conclusion for both unmixed forms,
all96 full-frame cases, and the twelve original1/3 deficient cases. -/
theorem physical_octahedral_separator :
    (∀ f : Fin 2, ∀ frame : Fin 4, ∀ order : Fin 6, ∃ q : Signature ℂ 4,
      Gadget.Realizes (markedResources (Fin.castAdd 2 f)
        (complexTensor (fullAncestor (Fin.castAdd 2 f) frame order))) .disequality q ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex q ∧ ∀ r : Fin 3, (flatten r q).rank=2) ∧
    (∀ f : Form, ∀ frame : Fin 4, ∀ order : Fin 6,
      Resolved f (complexTensor (fullAncestor f frame order))) ∧
    (∀ f : Fin 2, ∀ order : Fin 6, ∃ B : Native.Binary,
      Gadget.Realizes (markedResources (mixedForm f)
        (complexTensor (deficientAncestor (mixedForm f) order))) .disequality (Native.binarySignature B) ∧
      Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction (mixedForm f) (nativeTransfer B)) := by
  refine ⟨?_,full_reconstructed_exits,deficient_mixed_exits⟩
  intro f frame order
  exact standard_prime_eight_vertex f frame order _ (reconstructed_normalized _ _)

end
end Holant.Certificates.OctahedralSeparator
