import Holant.Pauli.ExoticKlein.SixPortAtlasCoverage
import Holant.Pauli.ExoticKlein.SixPortAtlasChecks
import Holant.Pauli.ExoticKlein.SixPortTheorem
import Holant.Pauli.ExoticKlein.EightPortAllCards

/-! Exact normalized survivor set for A.12(i). The seventeen entries are
proved exhaustive and pairwise projectively distinct, and each one has all
sixty actual safe cards. No finite-atlas premise is assumed. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open MatchingCard

def NormalizedSafe (h : Signature ℂ 6) : Prop := AllPhysicalSafe h ∧ BaseNormalized h

theorem candidate_normalized (i : Fin 17) : BaseNormalized (candidate i) :=
  good_normalized _ (candidate_good i)

theorem candidate_nonzero (i : Fin 17) : candidate i ≠ 0 :=
  baseNormalized_nonzero _ (candidate_normalized i)

theorem candidate_product (i : Fin 17) : IsProduct (candidate i) := by
  let j := candidateIndex i
  let c := Algebraic.gaussianToComplex (productScale j)
  have hc : c ≠ 0 := by
    intro hz
    apply candidate_nonzero i
    change (fun x => c*productTensor (productDirectionEquiv j) x) = 0
    rw [hz]
    funext x
    simp
  refine ⟨productMatching (productDirectionEquiv j).1 (productDirectionEquiv j).2.2.1,
    productLabels (productDirectionEquiv j),c,hc,?_⟩
  change (fun x => c*productTensor (productDirectionEquiv j) x) = _
  rw [productTensor_matching]

theorem product_safe (h : Signature ℂ 6) (hp : IsProduct h) : AllPhysicalSafe h := by
  obtain ⟨M,labels,c,hc,rfl⟩ := hp
  intro u v huv a
  have hh := contractPair_closed binaryGroup_projective X_mem binaryGroup_reversal u v (ne_of_lt huv)
    (asMatrix (dual a)) (dual_safe a) (fun x => c*M.tensor labels x)
    ((exotic_iff_group _).mp (Or.inr ⟨3,M,labels,c,hc,rfl⟩))
  have hcard : physicalCard u v a (fun x => c*M.tensor labels x) =
      contractPair u v (asMatrix (dual a)) (fun x => c*M.tensor labels x) := by
    funext x
    simp only [physicalCard,contractPair,insertPair_eq_fill u v (ne_of_lt huv),asMatrix,Matrix.of_apply]
  rw [hcard]
  rcases (exotic_iff_group _).mpr hh with hz | ⟨r,N,fixed,d,hd,he⟩
  · exact Or.inl hz
  · have hsize := N.port_card
    have hports := Fintype.card_congr (remainingOrder u v (ne_of_lt huv))
    simp only [Fintype.card_fin] at hports
    have hr : r = 2 := by omega
    subst r
    exact Or.inr ⟨N,fixed,d,hd,he⟩

theorem candidate_safe (i : Fin 17) : NormalizedSafe (candidate i) :=
  ⟨product_safe _ (candidate_product i),candidate_normalized i⟩

/-- The general product theorem is used only after all960literal product
directions and the exact integer first-card filter have been classified. -/
theorem complete (h : Signature ℂ 6) (hh : NormalizedSafe h) : ∃ i : Fin 17, h = candidate i := by
  have hp := six_port_product h (baseNormalized_nonzero h hh.2) hh.1
  obtain ⟨j,c,hc,he⟩ := canonical_product h hp
  have hn : BaseNormalized (fun x => c*productTensor (productDirectionEquiv j) x) := by
    rw [←he]
    exact hh.2
  obtain ⟨hgood,hscale⟩ := normalized_scaled_product j c hc hn
  obtain ⟨i,hi⟩ := (good_iff_candidate j).mp hgood
  refine ⟨i,?_⟩
  rw [he,hscale,←hi]
  rfl

theorem normalized_safe_iff (h : Signature ℂ 6) : NormalizedSafe h ↔ ∃ i : Fin 17, h = candidate i := by
  constructor
  · exact complete h
  · rintro ⟨i,rfl⟩
    exact candidate_safe i

def normalizedSafeEquiv : Fin 17 ≃ {h : Signature ℂ 6 // NormalizedSafe h} :=
  Equiv.ofBijective (fun i => ⟨candidate i,candidate_safe i⟩) (by
    constructor
    · intro i j he
      exact candidate_injective (congrArg Subtype.val he)
    · intro h
      obtain ⟨i,hi⟩ := complete h.val h.property
      exact ⟨i,Subtype.ext hi.symm⟩)

/-- Exactly seventeen actual normalized tensors, hence seventeen projective
lines because the fixed nonzero first card fixes the scalar uniquely. -/
theorem normalized_safe_card : Nat.card {h : Signature ℂ 6 // NormalizedSafe h} = 17 := by
  simpa using (Nat.card_congr normalizedSafeEquiv).symm

theorem candidate_projective_distinct (i j : Fin 17) (c : ℂ)
    (he : (fun x => c*candidate i x) = candidate j) : i = j := by
  have hb := congrArg (baseCard 0) he
  rw [baseCard_scale,candidate_normalized i,candidate_normalized j] at hb
  have hp := congrFun hb ((wordEquiv 4).symm 0)
  rw [base_pivot,mul_one] at hp
  have hc : c = 1 := hp
  apply candidate_injective
  simpa only [hc,one_mul] using he

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
