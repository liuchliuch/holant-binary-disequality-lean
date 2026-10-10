import Holant.ReedMuller.MatchingConsistency.Source

/-! The actual cross-card matching along one global equality edge. Its
internal weight-two entries are exactly the original W coefficients. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

 theorem cross_pair_coefficient_zero {f : Tensor K ι} (H : Consistent f)
    (u v k : ι) (huv : (weightGraph f).Adj u v) (huk : u≠k) (hvk : v≠k) :
    f (pairIndicator u k)=0 := by
  by_contra hh
  exact hvk (H.weight_matching u v k huv ⟨huk,hh⟩)

 theorem cross_card_nonzero (htwo : (2:K)≠0) {f : Tensor K ι} (H : Consistent f)
    (u v k : ι) (huv : (weightGraph f).Adj u v) (huk : u≠k) (hvk : v≠k) :
    card f u k false≠0 := by
  intro hz
  have hh := congrFun hz (fun _=>false)
  simp only [card,sameLift_false_zero,sameLift_true_zero,
    cross_pair_coefficient_zero H u v k huv huk hvk,Bool.false_eq_true,ite_false,
    one_mul,add_zero,Pi.zero_apply] at hh
  exact mul_ne_zero htwo H.constant_ne_zero hh

 theorem cross_card_internal_value {f : Tensor K ι} (H : Consistent f)
    (u v k : ι) (huv : (weightGraph f).Adj u v) (hvk : v≠k)
    (p q : Remaining u k) (hpv : p.val≠v) (hqv : q.val≠v) :
    card f u k false (pairIndicator p q)=2*f (pairIndicator p.val q.val) := by
  have hz : f (sameLift u k true (pairIndicator p q))=0 := by
    by_contra hh
    have he := H.global_equality u v huv _ hh
    have hv : sameLift u k true (pairIndicator p q) v=false := by
      have hm := sameLift_remaining u k true (pairIndicator p q) ⟨v,huv.1.symm,hvk⟩
      simpa only [pairIndicator,Subtype.ext_iff,Ne.symm hpv,Ne.symm hqv,false_or,
        decide_false] using hm
    rw [sameLift_left,hv] at he
    cases he
  simp only [card,Bool.false_eq_true,ite_false,one_mul,hz,add_zero,sameLift_pair]

/-- A matching of the actual cross card, tied to all unchanged original
weight-two coefficients away from the one retained mate. -/
structure CrossMatching (W : SimpleGraph ι) (u v k : ι) where
  pairing : Pairing (Remaining u k)
  internal : ∀p q : Remaining u k,p.val≠v → q.val≠v →
    (pairing.mate p=q ↔ W.Adj p.val q.val)

 theorem actual_cross_matching (htwo : (2:K)≠0) {f : Tensor K ι}
    (H : Consistent f) (hd : EqualityDeck f) (u v k : ι)
    (huv : (weightGraph f).Adj u v) (huk : u≠k) (hvk : v≠k) :
    Nonempty (CrossMatching (weightGraph f) u v k) := by
  obtain ⟨P,hP⟩ := (hd u k huk false).resolve_left (cross_card_nonzero htwo H u v k huv huk hvk)
  refine ⟨⟨P,?_⟩⟩
  intro p q hpv hqv
  by_cases hpq : p=q
  · subst q
    exact iff_of_false (P.ne_self p) (fun h => h.1 rfl)
  · have hvals : p.val≠q.val := fun h => hpq (Subtype.ext h)
    rw [←P.support_pair_iff p q hpq,←hP,cross_card_internal_value H u v k huv hvk p q hpv hqv]
    change 2*f (pairIndicator p.val q.val)≠0 ↔ p.val≠q.val ∧ f (pairIndicator p.val q.val)≠0
    rw [mul_ne_zero_iff]
    exact ⟨fun h => ⟨hvals,h.2⟩,fun h => ⟨htwo,h.2⟩⟩

end Holant.ReedMuller.WeightTwoIntegration
