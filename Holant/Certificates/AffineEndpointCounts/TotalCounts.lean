import Holant.Certificates.AffineEndpointCounts.CoreCounts
import Holant.Certificates.AffineEndpoint.CoreSource
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def retainedPairCodes : Set (Fin 18 × InputCode) :=
  {p | p.2 ∈ retainedInputCodes (numberedCore p.1)}

def retainedPairEquiv : retainedPairCodes ≃
    (k : Fin 18) × {c : InputCode // c ∈ retainedInputCodes (numberedCore k)} where
  toFun p := ⟨p.val.1,⟨p.val.2,p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem retained_pair_code_count : retainedPairCodes.ncard=4200 := by
  rw [←Nat.card_coe_set_eq,Nat.card_congr retainedPairEquiv,Nat.card_sigma]
  simp only [Nat.card_coe_set_eq,←retainedInputs_count,all_core_retained_counts]
  decide +kernel

def actualRetainedPairs : Set (Matrix Bool Bool AlgebraicComplex × Sig) :=
  {p | SourceCore p.1 ∧ p.2 ∈ normalizedAffineSet ∧
    EndpointEven (Signature.coordinateAction (fun _ => p.1) p.2)}

def actualPair (p : Fin 18 × InputCode) : Matrix Bool Bool AlgebraicComplex × Sig :=
  (coreMatrix (numberedCore p.1),inputSignature p.2)

theorem actualPair_injective : Function.Injective actualPair := by
  intro p q h
  apply Prod.ext
  · exact numberedCore_bijective.1 (coreMatrix_injective (congrArg Prod.fst h))
  · exact inputSignature_injective (congrArg Prod.snd h)

theorem actualRetainedPairs_eq_image : actualRetainedPairs=actualPair '' retainedPairCodes := by
  ext p
  constructor
  · rintro ⟨hK,hf,hg⟩
    obtain ⟨k,hk⟩ := source_core_complete p.1 hK
    obtain ⟨j,rfl⟩ := numberedCore_bijective.2 k
    obtain ⟨c,hc⟩ := normalizedAffineSet_eq_range ▸ hf
    refine ⟨(j,c),?_,?_⟩
    · change EndpointEven (coreAction _ _)
      simpa only [coreAction,hk,hc] using hg
    · exact Prod.ext hk hc
  · rintro ⟨⟨k,c⟩,hc,rfl⟩
    exact ⟨coreMatrix_source _,⟨inputSignature_affine c,inputSignature_ne_zero c,inputSignature_normalized c⟩,hc⟩

theorem actual_retained_pair_count : actualRetainedPairs.ncard=4200 := by
  rw [actualRetainedPairs_eq_image,Set.ncard_image_of_injective _ actualPair_injective,
    retained_pair_code_count]

def actualCoreRetained (K : Matrix Bool Bool AlgebraicComplex) : Set Sig :=
  {f | f ∈ normalizedAffineSet ∧ EndpointEven (Signature.coordinateAction (fun _ => K) f)}

def coresRetaining (n : Nat) : Set (Matrix Bool Bool AlgebraicComplex) :=
  {K | SourceCore K ∧ (actualCoreRetained K).ncard=n}

theorem coresRetaining_eq_image (n : Nat) :
    coresRetaining n=(fun k => coreMatrix (numberedCore k)) ''
      {k : Fin 18 | coreRetainedCount k=n} := by
  ext K
  constructor
  · rintro ⟨hK,hc⟩
    obtain ⟨k,rfl⟩ := source_core_complete K hK
    obtain ⟨j,rfl⟩ := numberedCore_bijective.2 k
    refine ⟨j,?_,rfl⟩
    exact (all_core_retained_counts j).symm.trans hc
  · rintro ⟨k,hk,rfl⟩
    exact ⟨coreMatrix_source _,(all_core_retained_counts k).trans hk⟩

theorem core_retention_histogram : (coresRetaining 612).ncard=6 ∧ (coresRetaining 44).ncard=12 := by
  have hi : Function.Injective (fun k : Fin 18 => coreMatrix (numberedCore k)) :=
    coreMatrix_injective.comp numberedCore_bijective.1
  have hc (n : Nat) : {k : Fin 18 | coreRetainedCount k=n}.ncard=
      (Finset.univ.filter (fun k : Fin 18 => coreRetainedCount k=n)).card := by
    rw [←Nat.card_coe_set_eq,Nat.card_eq_fintype_card,Fintype.card_subtype]
    congr 1
  rw [coresRetaining_eq_image,coresRetaining_eq_image,
    Set.ncard_image_of_injective _ hi,Set.ncard_image_of_injective _ hi,hc,hc]
  decide +kernel

def allCoreInputPairs : Set (Matrix Bool Bool AlgebraicComplex × Sig) :=
  {K | SourceCore K} ×ˢ normalizedAffineSet

theorem all_core_input_pair_count : allCoreInputPairs.ncard=660960 := by
  rw [allCoreInputPairs,Set.ncard_prod,source_core_count,normalized_affine_count]

end
end Holant.Certificates.AffineEndpointCounts
