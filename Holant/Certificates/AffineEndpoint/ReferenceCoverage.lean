import Holant.Certificates.AffineEndpoint.InputUniqueness
import Holant.Certificates.AffineEndpoint.OutputComplement

/-! Exact, duplicate-free coverage of every normalized affine reference. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.Certificates.AffineReference Holant.Certificates.FourthRootOdd
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

 def referenceInputTag (c : InputCode) : Nat :=
  if c.1=128 then c.2.val else if c.1=204 then 4+c.2.val else
  if c.1=236 then 36+c.2.val else if c.1=248 then 68+c.2.val else 100+c.2.val

 theorem referenceInput_tag (r : Fin 612) : referenceInputTag (referenceInput r)=r.val := by
  unfold referenceInput
  split_ifs <;> simp [referenceInputTag] <;> omega

 theorem referenceInput_injective : Function.Injective referenceInput := by
  intro r s he
  apply Fin.ext
  simpa only [referenceInput_tag] using congrArg referenceInputTag he

 theorem reference_injective : Function.Injective reference := by
  intro r s he
  exact referenceInput_injective (inputSignature_injective he)

 def referenceSupportIndices : Finset SupportIndex := {128,204,236,248,304}

 theorem reference_support_index_check : ∀s : SupportIndex,
    ((∀x,x∈supportWords s ↔ x=zeroWord ∨ x=oneWord) ∨
      (∃b : Fin 3,∀x,x∈supportWords s ↔ OnPlane b x) ∨
      (∀x,x∈supportWords s ↔ evenWord x=true)) → s∈referenceSupportIndices := by decide +kernel

 theorem input_reference_index (c : InputCode) (hs : ReferenceSupport (inputSignature c)) :
    c.1∈referenceSupportIndices := by
  apply reference_support_index_check
  rcases hs with he|⟨b,hb⟩|hf
  · exact Or.inl (fun x => (inputSignature_support c x).symm.trans (he x))
  · exact Or.inr (Or.inl ⟨b,fun x => (inputSignature_support c x).symm.trans (hb x)⟩)
  · exact Or.inr (Or.inr (fun x => (inputSignature_support c x).symm.trans (hf x)))

 theorem referenceInput_zero (c : Fin 4) : referenceInput ⟨c.val,by omega⟩=⟨128,c⟩ := by
  simp [referenceInput,c.isLt]

 theorem referenceInput_first_plane (c : Fin 32) : referenceInput ⟨c.val+4,by omega⟩=⟨204,c⟩ := by
  have h0 : ¬c.val+4<4 := by omega
  have h1 : c.val+4<36 := by omega
  simp [referenceInput,h0,h1]

 theorem referenceInput_second_plane (c : Fin 32) : referenceInput ⟨c.val+36,by omega⟩=⟨236,c⟩ := by
  have h0 : ¬c.val+36<4 := by omega
  have h1 : ¬c.val+36<36 := by omega
  have h2 : c.val+36<68 := by omega
  simp [referenceInput,h0,h1,h2]

 theorem referenceInput_third_plane (c : Fin 32) : referenceInput ⟨c.val+68,by omega⟩=⟨248,c⟩ := by
  have h0 : ¬c.val+68<4 := by omega
  have h1 : ¬c.val+68<36 := by omega
  have h2 : ¬c.val+68<68 := by omega
  have h3 : c.val+68<100 := by omega
  simp [referenceInput,h0,h1,h2,h3]

 theorem referenceInput_full (c : Fin 512) : referenceInput ⟨c.val+100,by omega⟩=⟨304,c⟩ := by
  have h0 : ¬c.val+100<4 := by omega
  have h1 : ¬c.val+100<36 := by omega
  have h2 : ¬c.val+100<68 := by omega
  have h3 : ¬c.val+100<100 := by omega
  simp [referenceInput,h0,h1,h2,h3]

 theorem referenceInput_coverage (c : InputCode) (hs : c.1∈referenceSupportIndices) :
    ∃r : Fin 612,referenceInput r=c := by
  obtain ⟨s,c⟩ := c
  simp only [referenceSupportIndices,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl
  · exact ⟨_,referenceInput_zero c⟩
  · exact ⟨_,referenceInput_first_plane c⟩
  · exact ⟨_,referenceInput_second_plane c⟩
  · exact ⟨_,referenceInput_third_plane c⟩
  · exact ⟨_,referenceInput_full c⟩

 theorem zero_normalized_is_canonical (f : Signature AlgebraicComplex 4) (h0 : f zeroWord=1) :
    CanonicalNormalized f := by
  intro a ha hleast
  have hn0 : f zeroWord≠0 := by rw [h0]; exact one_ne_zero
  have hcode := hleast zeroWord hn0
  have hzero : wordCode zeroWord=0 := by decide
  rw [hzero] at hcode
  have he : wordCode a=wordCode zeroWord := by rw [hzero]; exact le_antisymm hcode (Fin.zero_le _)
  rw [wordCode_injective he,h0]

 theorem reference_coverage (h : Signature AlgebraicComplex 4) (ha : Affine h)
    (h0 : h zeroWord=1) (hs : ReferenceSupport h) : ∃r : Fin 612,h=reference r := by
  have hn : h≠0 := by intro hz; have h1 := congrFun hz zeroWord; rw [h0] at h1; exact one_ne_zero h1
  obtain ⟨c,rfl⟩ := normalized_input_coverage h ha hn (zero_normalized_is_canonical h h0)
  obtain ⟨r,hr⟩ := referenceInput_coverage c (input_reference_index c hs)
  exact ⟨r,congrArg inputSignature hr.symm⟩

 def normalizedReferenceSet : Set (Signature AlgebraicComplex 4) :=
  {h | Affine h ∧ h zeroWord=1 ∧ ReferenceSupport h}

 theorem normalizedReferenceSet_eq_range : normalizedReferenceSet=Set.range reference := by
  ext h
  constructor
  · rintro ⟨ha,h0,hs⟩
    obtain ⟨r,hr⟩ := reference_coverage h ha h0 hs
    exact ⟨r,hr.symm⟩
  · rintro ⟨r,rfl⟩
    exact ⟨reference_affine r,reference_origin r,reference_support r⟩

 theorem normalized_reference_count : normalizedReferenceSet.ncard=612 := by
  rw [normalizedReferenceSet_eq_range,Set.ncard_range_of_injective reference_injective,Nat.card_eq_fintype_card]
  exact Fintype.card_fin 612

end
end Holant.Certificates.AffineEndpoint
