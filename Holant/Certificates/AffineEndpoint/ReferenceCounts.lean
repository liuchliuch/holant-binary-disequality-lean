import Holant.Certificates.AffineEndpoint.ReferenceCoverage

/-! The 4/96/512 histogram counts actual normalized reference signatures,
using proved injectivity and arbitrary-input coverage. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable SupportCatalog
open Holant.Certificates.AffineReference
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

 theorem reference_support_size (r : Fin 612) :
    supportSize (reference r)=2^supportDim (referenceInput r).1 := by
  classical
  have hs : (Finset.univ.filter (fun x : Fin 4 → Bool => reference r x≠0))=
      supportWords (referenceInput r).1 := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact inputSignature_support (referenceInput r) x
  rw [supportSize,hs,supportWords_card]

 def referenceSizeIndices (n : Nat) : Finset (Fin 612) :=
  Finset.univ.filter (fun r => 2^supportDim (referenceInput r).1=n)

 def referenceSizeSet (n : Nat) : Set (Signature AlgebraicComplex 4) :=
  {h | h∈normalizedReferenceSet ∧ supportSize h=n}

 theorem referenceSizeSet_eq_image (n : Nat) :
    referenceSizeSet n=reference '' (referenceSizeIndices n : Set (Fin 612)) := by
  ext h
  constructor
  · rintro ⟨⟨ha,h0,hs⟩,hn⟩
    obtain ⟨r,rfl⟩ := reference_coverage h ha h0 hs
    exact ⟨r,by simpa only [referenceSizeIndices,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,
      true_and,reference_support_size] using hn,rfl⟩
  · rintro ⟨r,hr,rfl⟩
    refine ⟨⟨reference_affine r,reference_origin r,reference_support r⟩,?_⟩
    simpa only [referenceSizeIndices,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,
      true_and,reference_support_size] using hr

 theorem reference_size_count (n : Nat) : (referenceSizeSet n).ncard=(referenceSizeIndices n).card := by
  rw [referenceSizeSet_eq_image,Set.ncard_image_of_injective _ reference_injective,Set.ncard_coe_finset]

 theorem reference_index_histogram :
    (referenceSizeIndices 2).card=4 ∧ (referenceSizeIndices 4).card=96 ∧
      (referenceSizeIndices 8).card=512 := by decide +kernel

 theorem normalized_reference_histogram :
    (referenceSizeSet 2).ncard=4 ∧ (referenceSizeSet 4).ncard=96 ∧
      (referenceSizeSet 8).ncard=512 := by
  simpa only [reference_size_count] using reference_index_histogram

end
end Holant.Certificates.AffineEndpoint
