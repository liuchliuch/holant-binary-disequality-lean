import Holant.ReedMuller.WeightTwoIntegration.Perfection

/-! Full support of the cross card comes from its actual matching, and its
only compatible lift is the original word. This precludes cancellation. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

 theorem actual_cross_matching_data (htwo : (2:K)≠0) {f : Tensor K ι}
    (H : Consistent f) (hd : EqualityDeck f) (u v k : ι)
    (huv : (weightGraph f).Adj u v) (huk : u≠k) (hvk : v≠k) :
    ∃ C : CrossMatching (weightGraph f) u v k,∀y,card f u k false y≠0 ↔ C.pairing.Support y := by
  obtain ⟨P,hP⟩ := (hd u k huk false).resolve_left (cross_card_nonzero htwo H u v k huv huk hvk)
  have hi : ∀p q : Remaining u k,p.val≠v → q.val≠v →
      (P.mate p=q ↔ (weightGraph f).Adj p.val q.val) := by
    intro p q hpv hqv
    by_cases hpq : p=q
    · subst q
      exact iff_of_false (P.ne_self p) (fun h => h.1 rfl)
    · have hvals : p.val≠q.val := fun h => hpq (Subtype.ext h)
      rw [←P.support_pair_iff p q hpq,←hP,cross_card_internal_value H u v k huv hvk p q hpv hqv]
      change 2*f (pairIndicator p.val q.val)≠0 ↔ p.val≠q.val ∧ f (pairIndicator p.val q.val)≠0
      rw [mul_ne_zero_iff]
      exact ⟨fun h => ⟨hvals,h.2⟩,fun h => ⟨htwo,h.2⟩⟩
  exact ⟨⟨P,hi⟩,hP⟩

 theorem CrossMatching.support_of_equalities {W : SimpleGraph ι}
    (hmatch : ∀u v w,W.Adj u v → W.Adj u w → v=w)
    (u v k z : ι) (huv : W.Adj u v) (hkz : W.Adj k z) (huk : u≠k) (hvk : v≠k)
    (C : CrossMatching W u v k) (x : ι → Bool)
    (hx : ∀p q,W.Adj p q → x p=x q) (hcross : x u=x k) :
    C.pairing.Support (fun p => x p.val) := by
  have hzu : z≠u := by
    intro he
    have hku : W.Adj k u := he ▸ hkz
    exact hvk (hmatch u v k huv hku.symm)
  have hzv : z≠v := by
    intro he
    have hkv : W.Adj k v := he ▸ hkz
    exact huk (hmatch v u k huv.symm hkv.symm)
  let v' : Remaining u k := ⟨v,huv.ne.symm,hvk⟩
  let z' : Remaining u k := ⟨z,hzu,hkz.ne.symm⟩
  have hmate : C.pairing.mate z'=v' := by
    apply Subtype.ext
    by_contra he
    have hw := (C.internal z' (C.pairing.mate z') hzv he).mp rfl
    have heq := hmatch z k (C.pairing.mate z').val hkz.symm hw
    exact (C.pairing.mate z').property.2 heq.symm
  have hzx : x z=x v := (hx z k hkz.symm).trans (hcross.symm.trans (hx u v huv))
  intro p
  by_cases hpv : p.val=v
  · have hp : p=v' := Subtype.ext hpv
    have hv : C.pairing.mate v'=z' := (C.pairing.mate_eq_iff z' v').mp hmate
    rw [hp,hv]
    exact hzx
  · by_cases hqv : (C.pairing.mate p).val=v
    · have hq : C.pairing.mate p=v' := Subtype.ext hqv
      have hp : p=z' := C.pairing.injective (hq.trans hmate.symm)
      rw [hp,hmate]
      exact hzx.symm
    · exact (hx _ _ ((C.internal p (C.pairing.mate p) hpv hqv).mp rfl)).symm

 theorem cross_unique_lift {f : Tensor K ι} (H : Consistent f)
    (u v k : ι) (huv : (weightGraph f).Adj u v) (hvk : v≠k)
    (x : ι → Bool) (hxuv : x u=x v) (hxuk : x u=x k) :
    card f u k false (fun p => x p.val)=2*f x := by
  let y : Remaining u k → Bool := fun p => x p.val
  have hz (b : Bool) (hb : b≠x u) : f (sameLift u k b y)=0 := by
    by_contra hh
    have he := H.global_equality u v huv _ hh
    have hv := sameLift_remaining u k b y ⟨v,huv.ne.symm,hvk⟩
    rw [sameLift_left,hv] at he
    exact hb (he.trans hxuv.symm)
  have hr : sameLift u k (x u) y=x := sameLift_reconstruct u k x hxuk
  cases hb : x u
  · have hh := hz true (by simp [hb])
    rw [hb] at hr
    change 2*(f (sameLift u k false y)+1*f (sameLift u k true y))=_
    rw [hr,hh,mul_zero,add_zero]
  · have hh := hz false (by simp [hb])
    rw [hb] at hr
    change 2*(f (sameLift u k false y)+1*f (sameLift u k true y))=_
    rw [hr,hh,one_mul,zero_add]

 theorem cross_support_nonzero (htwo : (2:K)≠0) {f : Tensor K ι}
    (H : Consistent f) (hd : EqualityDeck f) (u v k z : ι)
    (huv : (weightGraph f).Adj u v) (hkz : (weightGraph f).Adj k z) (huk : u≠k) (hvk : v≠k)
    (x : ι → Bool) (hx : ∀p q,(weightGraph f).Adj p q → x p=x q) (hcross : x u=x k) : f x≠0 := by
  obtain ⟨C,hC⟩ := actual_cross_matching_data htwo H hd u v k huv huk hvk
  have h := (hC (fun p => x p.val)).mpr
    (C.support_of_equalities H.weight_matching u v k z huv hkz huk hvk x hx hcross)
  rw [cross_unique_lift H u v k huv hvk x (hx u v huv) hcross] at h
  exact (mul_ne_zero_iff.mp h).2

end Holant.ReedMuller.WeightTwoIntegration
