import Holant.ReedMuller.MatchingConsistency.Coefficients
import Holant.ReedMuller.MatchingConsistency.LocalGraph

/-! The original two-card equations construct the local graph cover.
Neither the common matching nor its agreement is an input. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph
variable {ι K : Type*} [DecidableEq ι] [Field K]

 theorem SelectedMatching.pair_iff {q : Tensor K ι} (S : SelectedMatching q)
    (u v : ι) (huv : u≠v) : q (pairIndicator u v)≠0 ↔ optionalAdj S.pairing u v := by
  rw [S.exact]
  simp only [Pairing.support_pair_iff _ _ _ huv,optionalAdj]

 theorem optionalAdj_ne {P : Option (Pairing ι)} {u v : ι} (h : optionalAdj P u v) : u≠v := by
  rintro rfl
  obtain ⟨M,hM,he⟩ := h
  exact M.ne_self u he

 def EqualityDeck.localCover (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (i j : ι) (hij : i≠j) : LocalCover (weightGraph f) i j := by
  let P := (hdeck i j hij false).select
  let Q := (hdeck i j hij true).select
  refine ⟨P.pairing,Q.pairing,?_,?_,?_⟩
  · intro u v huv
    have hne : u≠v := fun he => huv.1 (congrArg Subtype.val he)
    have h := first_slice_card_cover htwo f i j (pairIndicator u v) (by
      rw [sameLift_pair]
      exact huv.2)
    exact h.imp ((P.pair_iff u v hne).mp) ((Q.pair_iff u v hne).mp)
  · intro u v hp hq
    have hne := optionalAdj_ne hp
    refine ⟨fun he => hne (Subtype.ext he),?_⟩
    have hp' := (P.pair_iff u v hne).mpr hp
    have hq' : card f i j true (pairIndicator u v)=0 := by
      by_contra hh
      exact hq ((Q.pair_iff u v hne).mp hh)
    have h := left_only_slice f i j (pairIndicator u v) hp' hq'
    rwa [sameLift_pair] at h
  · intro u v hq hp
    have hne := optionalAdj_ne hq
    refine ⟨fun he => hne (Subtype.ext he),?_⟩
    have hq' := (Q.pair_iff u v hne).mpr hq
    have hp' : card f i j false (pairIndicator u v)=0 := by
      by_contra hh
      exact hp ((P.pair_iff u v hne).mp hh)
    have h := right_only_slice f i j (pairIndicator u v) hq' hp'
    rwa [sameLift_pair] at h

 theorem EqualityDeck.weight_matching [Fintype ι] (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (hn : 6≤Fintype.card ι) :
    ∀u v w,(weightGraph f).Adj u v → (weightGraph f).Adj u w → v=w :=
  localCover_degree_le_one (weightGraph f) hn (fun i j hij => ⟨hdeck.localCover htwo i j hij⟩)

end Holant.ReedMuller.MatchingConsistency
