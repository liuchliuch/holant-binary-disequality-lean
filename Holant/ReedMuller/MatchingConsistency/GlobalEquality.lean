import Holant.ReedMuller.MatchingConsistency.Consequences

/-! The common support matching of each visible pair imposes every nonzero
original weight-two edge as a global equality on the original tensor. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

 theorem EqualityDeck.nonzero_cards_support_equal (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (hn : 6≤Fintype.card ι) (i j : ι) (hij : i≠j)
    (hp : card f i j false≠0) (hq : card f i j true≠0) :
    ∀x,card f i j false x≠0 ↔ card f i j true x≠0 := by
  obtain ⟨P,hP⟩ := (hdeck i j hij false).resolve_left hp
  obtain ⟨Q,hQ⟩ := (hdeck i j hij true).resolve_left hq
  have he := hdeck.card_matchings_agree htwo hn i j hij P Q hP hQ
  intro x
  rw [hP,hQ]
  simp only [Pairing.Support,he]

 theorem EqualityDeck.card_pair_of_weight_edge (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (hn : 6≤Fintype.card ι) (i j : ι) (hij : i≠j)
    (p q : Remaining i j) (hpq : (weightGraph f).Adj p.val q.val)
    (minus : Bool) (hcard : card f i j minus≠0) :
    card f i j minus (pairIndicator p q)≠0 := by
  have hc := first_slice_card_cover htwo f i j (pairIndicator p q) (by
    rw [sameLift_pair]
    exact hpq.2)
  cases minus
  · rcases hc with h | h
    · exact h
    · have hwhole : card f i j true≠0 := fun hh => h (congrFun hh _)
      exact (hdeck.nonzero_cards_support_equal htwo hn i j hij hcard hwhole _).mpr h
  · rcases hc with h | h
    · have hwhole : card f i j false≠0 := fun hh => h (congrFun hh _)
      exact (hdeck.nonzero_cards_support_equal htwo hn i j hij hwhole hcard _).mp h
    · exact h

 theorem EqualityDeck.global_equality (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (hn : 6≤Fintype.card ι) (p q : ι)
    (hpq : (weightGraph f).Adj p q) : ∀x,f x≠0 → x p=x q := by
  intro x hx
  by_contra hneq
  have hrem := remaining_card_add_two p q hpq.1
  obtain ⟨i,j,hij,hxij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Remaining p q => x k.val) (by simp only [Fintype.card_bool]; omega)
  have hij' : i.val≠j.val := fun h => hij (Subtype.ext h)
  let p' : Remaining i.val j.val := ⟨p,Ne.symm i.property.1,Ne.symm j.property.1⟩
  let q' : Remaining i.val j.val := ⟨q,Ne.symm i.property.2,Ne.symm j.property.2⟩
  have hpq' : p'≠q' := fun h => hpq.1 (congrArg Subtype.val h)
  let y : Remaining i.val j.val → Bool := fun k => x k.val
  have hz (minus : Bool) : card f i.val j.val minus y=0 := by
    by_contra hvalue
    have hwhole : card f i.val j.val minus≠0 := fun hh => hvalue (congrFun hh _)
    obtain ⟨M,hM⟩ := (hdeck i.val j.val hij' minus).resolve_left hwhole
    have hpair := hdeck.card_pair_of_weight_edge htwo hn i.val j.val hij' p' q' hpq minus hwhole
    have he := (M.support_pair_iff p' q' hpq').mp ((hM _).mp hpair)
    have hsame := (hM y).mp hvalue p'
    rw [he] at hsame
    exact hneq hsame.symm
  have hs := (card_both_zero_iff htwo f i.val j.val y).mp ⟨hz false,hz true⟩
  have hrec : sameLift i.val j.val (x i.val) y=x := sameLift_reconstruct _ _ x hxij
  have hzero : f (sameLift i.val j.val (x i.val) y)=0 := by
    cases hbit : x i.val
    · exact hs.1
    · exact hs.2
  exact hx (hrec ▸ hzero)

end Holant.ReedMuller.MatchingConsistency
