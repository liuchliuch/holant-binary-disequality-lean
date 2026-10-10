import Holant.ReedMuller.MatchingConsistency.Cover

/-! Matching agreement, the nonzero constant coefficient, and the resulting
global Walsh equalities, all derived from the literal two-card deck. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

 theorem EqualityDeck.card_matchings_agree (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (hn : 6≤Fintype.card ι) (i j : ι) (hij : i≠j)
    (P Q : Pairing (Remaining i j))
    (hP : ∀x,card f i j false x≠0 ↔ P.Support x)
    (hQ : ∀x,card f i j true x≠0 ↔ Q.Support x) : P.mate=Q.mate := by
  funext u
  by_contra hne
  have hp : u≠P.mate u := (P.ne_self u).symm
  have hq : u≠Q.mate u := (Q.ne_self u).symm
  have hpval : card f i j false (pairIndicator u (P.mate u))≠0 :=
    (hP _).mpr ((P.support_pair_iff _ _ hp).mpr rfl)
  have hqval : card f i j true (pairIndicator u (Q.mate u))≠0 :=
    (hQ _).mpr ((Q.support_pair_iff _ _ hq).mpr rfl)
  have hqzero : card f i j true (pairIndicator u (P.mate u))=0 := by
    by_contra h
    exact hne ((Q.support_pair_iff _ _ hp).mp ((hQ _).mp h)).symm
  have hpzero : card f i j false (pairIndicator u (Q.mate u))=0 := by
    by_contra h
    exact hne ((P.support_pair_iff _ _ hq).mp ((hP _).mp h))
  have hv : (weightGraph f).Adj u.val (P.mate u).val := by
    refine ⟨fun h => hp (Subtype.ext h),?_⟩
    have h := left_only_slice f i j _ hpval hqzero
    rwa [sameLift_pair] at h
  have hw : (weightGraph f).Adj u.val (Q.mate u).val := by
    refine ⟨fun h => hq (Subtype.ext h),?_⟩
    have h := right_only_slice f i j _ hqval hpzero
    rwa [sameLift_pair] at h
  exact hne (Subtype.ext (hdeck.weight_matching htwo hn _ _ _ hv hw))

 theorem EqualityDeck.constant_ne_zero (htwo : (2:K)≠0) {f : Tensor K ι}
    (hdeck : EqualityDeck f) (hn : 6≤Fintype.card ι) (hvisible : graph f=⊥) :
    f (fun _=>false)≠0 := by
  intro hz
  have hall (i j : ι) (hij : i≠j) : (weightGraph f).Adj i j := by
    refine ⟨hij,?_⟩
    intro hpair
    have hzero (minus : Bool) : card f i j minus (fun _=>false)=0 := by
      simp only [card,sameLift_false_zero,sameLift_true_zero,hz,hpair,mul_zero,add_zero]
    have hwhole (minus : Bool) : card f i j minus=0 := by
      by_contra hh
      exact hdeck.nonzeroAtZero i j hij minus hh (hzero minus)
    have hg := (graph_zero_cards htwo f i j hij).mpr ⟨hwhole false,hwhole true⟩
    rw [hvisible] at hg
    exact hg
  have hn' : 2<Fintype.card ι := by omega
  obtain ⟨u,v,w,huv,huw,hvw⟩ := Fintype.two_lt_card_iff.mp hn'
  exact hvw (hdeck.weight_matching htwo hn u v w (hall u v huv) (hall u w huw))

end Holant.ReedMuller.MatchingConsistency
