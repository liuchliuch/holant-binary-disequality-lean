import Holant.Certificates.AffineEndpointCounts.RetainedNegativeFalse
import Holant.Certificates.AffineEndpointCounts.RetainedNegativeTrue
import Holant.Certificates.AffineEndpointCounts.RetainedPositive
import Holant.Certificates.AffineEndpoint.InputUniqueness
import Holant.Certificates.AffineEndpoint.CoreAffine
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem candidate_pair_iff (b : Bool) (c : InputCode) :
    (c.1.val,c.2.val) ∈ candidatePairList b ↔ ∃j,candidateInput b j=c := by
  simp only [candidatePairList,List.mem_ofFn]
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j,?_⟩
    rcases c with ⟨s,c⟩
    have hs : (candidatePairs b j).1=s := Fin.ext (congrArg Prod.fst hj)
    apply Sigma.ext hs
    apply (Fin.heq_ext_iff (congrArg (fun s => phaseCodeCount (SupportCatalog.supportDim s)) hs)).mpr
    exact congrArg Prod.snd hj
  · rintro ⟨j,hj⟩
    exact ⟨j,by rw [←hj]; rfl⟩

theorem base_retained_iff_candidates (b : Bool) (c : InputCode) :
    BaseRetained c.1 c.2.val b ↔ ∃j,candidateInput b j=c := by
  constructor
  · intro hr
    apply (candidate_pair_iff b c).mp
    cases b
    · exact retained_false_complete c hr
    · exact retained_true_complete c hr
  · rintro ⟨j,rfl⟩
    exact candidate_retained b j

def retainedInputCodes (k : CoreIndex) : Set InputCode :=
  {c | EndpointEven (coreAction k (inputSignature c))}

def retainedInputs (k : CoreIndex) : Set (Signature AlgebraicComplex 4) :=
  {f | f ∈ normalizedAffineSet ∧ EndpointEven (coreAction k f)}

theorem retainedInputs_eq_image (k : CoreIndex) :
    retainedInputs k=inputSignature '' retainedInputCodes k := by
  ext f
  constructor
  · rintro ⟨hf,he⟩
    obtain ⟨c,rfl⟩ := normalizedAffineSet_eq_range ▸ hf
    exact ⟨c,he,rfl⟩
  · rintro ⟨c,hc,rfl⟩
    exact ⟨⟨inputSignature_affine c,inputSignature_ne_zero c,inputSignature_normalized c⟩,hc⟩

theorem retainedInputs_count (k : CoreIndex) :
    (retainedInputs k).ncard=(retainedInputCodes k).ncard := by
  rw [retainedInputs_eq_image,Set.ncard_image_of_injective _ inputSignature_injective]

theorem base_retained_set (b : Bool) :
    retainedInputCodes (numberedCore (baseCore b))=Set.range (candidateInput b) := by
  ext c
  change EndpointEven (Signature.coordinateAction _ _ ) ↔ _
  rw [←integerRetained_iff,←baseRetained_iff,base_retained_iff_candidates]
  rfl

theorem base_retained_count (b : Bool) :
    (retainedInputs (numberedCore (baseCore b))).ncard=44 := by
  rw [retainedInputs_count,base_retained_set,Set.ncard_range_of_injective (candidateInput_injective b)]
  rw [Nat.card_eq_fintype_card,Fintype.card_fin]

end
end Holant.Certificates.AffineEndpointCounts
