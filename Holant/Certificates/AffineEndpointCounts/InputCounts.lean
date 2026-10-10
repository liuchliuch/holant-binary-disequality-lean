import Holant.Certificates.AffineEndpoint.InputUniqueness
import Holant.Certificates.AffineEndpoint.ReferenceCounts
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.Certificates.AffineEndpoint
open Holant.Certificates.AffineReference AffineEndpoint.SupportCatalog
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem input_support_size (c : InputCode) :
    supportSize (inputSignature c)=2^supportDim c.1 := by
  classical
  have hs : (Finset.univ.filter (fun x : Fin 4 → Bool => inputSignature c x≠0))=supportWords c.1 := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact inputSignature_support c x
  rw [supportSize,hs,supportWords_card]

def normalizedDimensionSet (d : Nat) : Set (Signature AlgebraicComplex 4) :=
  {f | f ∈ normalizedAffineSet ∧ supportSize f=2^d}

theorem normalizedDimensionSet_eq_image (d : Nat) :
    normalizedDimensionSet d=inputSignature '' {c : InputCode | supportDim c.1=d} := by
  ext f
  constructor
  · rintro ⟨hf,hd⟩
    obtain ⟨c,rfl⟩ := normalizedAffineSet_eq_range ▸ hf
    refine ⟨c,?_,rfl⟩
    exact (Nat.pow_right_inj (by decide : 1 < 2)).mp ((input_support_size c).symm.trans hd)
  · rintro ⟨c,hc,rfl⟩
    exact ⟨⟨inputSignature_affine c,inputSignature_ne_zero c,inputSignature_normalized c⟩,
      (input_support_size c).trans (congrArg (fun d => 2^d) hc)⟩

theorem normalizedDimensionSet_card (d : Nat) :
    (normalizedDimensionSet d).ncard=Fintype.card {c : InputCode // supportDim c.1=d} := by
  rw [normalizedDimensionSet_eq_image,Set.ncard_image_of_injective _ inputSignature_injective,
    ←Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.refl _)

theorem actual_normalized_dimension_counts :
    (normalizedDimensionSet 0).ncard=16 ∧ (normalizedDimensionSet 1).ncard=480 ∧
    (normalizedDimensionSet 2).ncard=4480 ∧ (normalizedDimensionSet 3).ncard=15360 ∧
    (normalizedDimensionSet 4).ncard=16384 := by
  simpa only [normalizedDimensionSet_card] using normalized_input_dimension_counts

end
end Holant.Certificates.AffineEndpointCounts
