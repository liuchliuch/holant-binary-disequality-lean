import Holant.ReedMuller.SupportReconstruction.Products
import Holant.ReedMuller.WeightTwoIntegration.SamePairSupport

/-! With zero weight-two coefficients, both actual normalized cards survive
at value2 at zero. Their weighted products and common matching are derived. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.WeightTwoIntegration
variable {K ι : Type*} [Field K] [DecidableEq ι]

 theorem pair_coefficient_zero (f : Tensor K ι) (hW : weightGraph f=⊥) (i j : ι) (hij : i≠j) :
    f (pairIndicator i j)=0 := by
  by_contra h
  have he : (weightGraph f).Adj i j := ⟨hij,h⟩
  rw [hW] at he
  exact he

 theorem card_zero_value (f : Tensor K ι) (h0 : f (fun _=>false)=1) (hW : weightGraph f=⊥)
    (i j : ι) (hij : i≠j) (minus : Bool) : card f i j minus (fun _=>false)=2 := by
  simp only [card,sameLift_false_zero,sameLift_true_zero,h0,pair_coefficient_zero f hW i j hij,
    mul_zero,add_zero,mul_one]

 structure MatchingCards (f : Tensor K ι) (i j : ι) where
  plus : WeightedProduct K (Remaining i j)
  minus : WeightedProduct K (Remaining i j)
  plus_eq : card f i j false=plus.value
  minus_eq : card f i j true=minus.value
  matching : (Pairing.ofPorts plus.ports).mate=(Pairing.ofPorts minus.ports).mate
  plus_zero : plus.value (fun _=>false)=2
  minus_zero : minus.value (fun _=>false)=2

 theorem actual_matching_cards (htwo : (2:K)≠0) (f : Tensor K ι) (H : Consistent f)
    (hw : WeightedDeck f) (h0 : f (fun _=>false)=1) (hW : weightGraph f=⊥)
    (i j : ι) (hij : i≠j) : Nonempty (MatchingCards f i j) := by
  have hn (minus : Bool) : card f i j minus≠0 := by
    intro h
    have hh := congrFun h (fun _=>false)
    rw [card_zero_value f h0 hW i j hij minus] at hh
    exact htwo hh
  obtain ⟨P,hP⟩ := (hw i j hij false).resolve_left (hn false)
  obtain ⟨Q,hQ⟩ := (hw i j hij true).resolve_left (hn true)
  refine ⟨⟨P,Q,hP,hQ,?_,?_,?_⟩⟩
  · apply H.card_matchings_agree i j hij
    · intro x; rw [hP]; exact P.support_spec x
    · intro x; rw [hQ]; exact Q.support_spec x
  · rw [←hP]
    exact card_zero_value f h0 hW i j hij false
  · rw [←hQ]
    exact card_zero_value f h0 hW i j hij true

 theorem MatchingCards.minus_logical_nonzero {f : Tensor K ι} {i j : ι}
    (D : MatchingCards f i j) (t : Fin D.plus.edges → Bool) : D.minus.value (logicalWord D.plus t)≠0 := by
  apply (D.minus.support_spec _).mpr
  have h := (D.plus.support_spec _).mp (logical_supported D.plus t)
  change ∀p,logicalWord D.plus t ((Pairing.ofPorts D.minus.ports).mate p)=logicalWord D.plus t p
  rw [←D.matching]
  exact h

end Holant.ReedMuller.SupportReconstruction
