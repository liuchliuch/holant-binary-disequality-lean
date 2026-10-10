import Holant.Certificates.AffineEndpointCounts.RetainedCounts
import Holant.Certificates.AffineEndpointCounts.CorePermutations
import Holant.Certificates.AffineEndpoint.ReferenceCounts
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def endpointInputCodes : Set InputCode := {c | EndpointEven (inputSignature c)}

theorem zeroWord_le_code : ∀x : Fin 4 → Bool,wordCode zeroWord ≤ wordCode x := by decide +kernel

theorem endpointInputCodes_eq : endpointInputCodes = Set.range referenceInput := by
  ext c
  constructor
  · intro hc
    have h0 := inputSignature_normalized c zeroWord hc.1 (fun x _ => zeroWord_le_code x)
    obtain ⟨r,he⟩ := reference_coverage (inputSignature c) (inputSignature_affine c) h0
      (affine_endpoint_reference_support _ (inputSignature_affine c) hc)
    exact ⟨r,inputSignature_injective he.symm⟩
  · rintro ⟨r,rfl⟩
    exact reference_endpoint_even r

theorem endpoint_input_count : endpointInputCodes.ncard = 612 := by
  rw [endpointInputCodes_eq,Set.ncard_range_of_injective referenceInput_injective,
    Nat.card_eq_fintype_card,Fintype.card_fin]

theorem inputEquiv_endpoint_iff (T : ProjectiveAffineAutomorphism) (c : InputCode) :
    EndpointEven (T.forward.toFun (inputSignature c)) ↔ T.inputEquiv c ∈ endpointInputCodes := by
  obtain ⟨a,ha,he⟩ := T.inputEquiv_spec c
  rw [he,endpointEven_scale_iff _ _ ha]
  rfl

theorem affine_automorphism_count (T : ProjectiveAffineAutomorphism) :
    {c : InputCode | EndpointEven (T.forward.toFun (inputSignature c))}.ncard = 612 := by
  have he : {c : InputCode | EndpointEven (T.forward.toFun (inputSignature c))} =
      T.inputEquiv ⁻¹' endpointInputCodes := by ext c; exact inputEquiv_endpoint_iff T c
  rw [he,Set.ncard_preimage_of_injective_subset_range T.inputEquiv.injective
    (fun c _ => T.inputEquiv.surjective c),endpoint_input_count]

theorem core_count_from_automorphism (k : CoreIndex) (T : ProjectiveAffineAutomorphism)
    (he : ∀f,T.forward.toFun f = coreAction k f) : (retainedInputs k).ncard = 612 := by
  rw [retainedInputs_count]
  have hs : retainedInputCodes k = {c : InputCode | EndpointEven (T.forward.toFun (inputSignature c))} := by
    ext c
    simp only [retainedInputCodes,Set.mem_setOf_eq,he]
  rw [hs,affine_automorphism_count]

theorem identity_retained_count : (retainedInputs (.inl 0)).ncard = 612 := by
  rw [retainedInputs_count]
  have he : retainedInputCodes (.inl 0) = endpointInputCodes := by
    ext c
    simp only [retainedInputCodes,endpointInputCodes,Set.mem_setOf_eq,coreAction_identity]
  rw [he,endpoint_input_count]

theorem flip_retained_count : (retainedInputs (.inl 1)).ncard = 612 :=
  core_count_from_automorphism _ flipAutomorphism (fun f => (coreAction_flip f).symm)

theorem even_hadamard_retained_count (j : Fin 4) :
    (retainedInputs (.inr (.inl ⟨2*j.val,by omega⟩))).ncard = 612 :=
  core_count_from_automorphism _ (evenHadamardAutomorphism j) (evenHadamard_forward j)

theorem twisted_base_iff (b : Bool) (j : Fin 4) (c : InputCode) :
    EndpointEven (coreAction (numberedCore (baseCore b)) (phaseTwist j (inputSignature c))) ↔
      (phaseAutomorphism j).inputEquiv c ∈ retainedInputCodes (numberedCore (baseCore b)) := by
  obtain ⟨a,ha,he⟩ := (phaseAutomorphism j).inputEquiv_spec c
  change phaseTwist j (inputSignature c) = _ at he
  rw [he]
  unfold coreAction
  rw [coordinateAction_scale,endpointEven_scale_iff _ _ ha]
  rfl

theorem twisted_base_count (b : Bool) (j : Fin 4) :
    {c : InputCode | EndpointEven (coreAction (numberedCore (baseCore b))
      (phaseTwist j (inputSignature c)))}.ncard = 44 := by
  have he : {c : InputCode | EndpointEven (coreAction (numberedCore (baseCore b))
      (phaseTwist j (inputSignature c)))} = (phaseAutomorphism j).inputEquiv ⁻¹'
        retainedInputCodes (numberedCore (baseCore b)) := by ext c; exact twisted_base_iff b j c
  rw [he,Set.ncard_preimage_of_injective_subset_range (phaseAutomorphism j).inputEquiv.injective
    (fun c _ => (phaseAutomorphism j).inputEquiv.surjective c),←retainedInputs_count,base_retained_count]

theorem odd_hadamard_retained_count (j : Fin 4) :
    (retainedInputs (.inr (.inl ⟨2*j.val+1,by omega⟩))).ncard = 44 := by
  rw [retainedInputs_count]
  have he : retainedInputCodes (.inr (.inl ⟨2*j.val+1,by omega⟩)) =
      {c : InputCode | EndpointEven (coreAction (numberedCore (baseCore false))
        (phaseTwist j (inputSignature c)))} := by
    ext c
    simp only [retainedInputCodes,Set.mem_setOf_eq,coreAction_hadamard_odd]
    rfl
  rw [he,twisted_base_count]

theorem mixed_retained_count (j : Fin 4) (b : Bool) :
    (retainedInputs (.inr (.inr (j,b)))).ncard = 44 := by
  rw [retainedInputs_count]
  have he : retainedInputCodes (.inr (.inr (j,b))) =
      {c : InputCode | EndpointEven (coreAction (numberedCore (baseCore true))
        (phaseTwist j (inputSignature c)))} := by
    ext c
    cases b
    · simp only [retainedInputCodes,Set.mem_setOf_eq,coreAction_mixed_positive]
      rfl
    · simp only [retainedInputCodes,Set.mem_setOf_eq,coreAction_mixed_negative,endpointEven_complement_iff]
      rfl
  rw [he,twisted_base_count]

def coreRetainedCount (k : Fin 18) : Nat :=
  if k=0 ∨ k=1 ∨ k=2 ∨ k=4 ∨ k=6 ∨ k=8 then 612 else 44

theorem all_core_retained_counts (k : Fin 18) :
    (retainedInputs (numberedCore k)).ncard = coreRetainedCount k := by
  fin_cases k
  · exact identity_retained_count
  · exact flip_retained_count
  · exact even_hadamard_retained_count 0
  · exact odd_hadamard_retained_count 0
  · exact even_hadamard_retained_count 1
  · exact odd_hadamard_retained_count 1
  · exact even_hadamard_retained_count 2
  · exact odd_hadamard_retained_count 2
  · exact even_hadamard_retained_count 3
  · exact odd_hadamard_retained_count 3
  · exact mixed_retained_count 0 false
  · exact mixed_retained_count 0 true
  · exact mixed_retained_count 1 false
  · exact mixed_retained_count 1 true
  · exact mixed_retained_count 2 false
  · exact mixed_retained_count 2 true
  · exact mixed_retained_count 3 false
  · exact mixed_retained_count 3 true

end
end Holant.Certificates.AffineEndpointCounts
