import Holant.ReedMuller.MatchingConsistency.Deck

/-! Literal weight-two coefficients and the two-card linear identities. -/
noncomputable section
namespace Holant.ReedMuller.MatchingConsistency
open Holant Holant.ReedMuller.ZeroCardGraph
variable {ι K : Type*} [DecidableEq ι] [Field K]

 theorem pairIndicator_comm (u v : ι) : pairIndicator u v=pairIndicator v u := by
  funext k
  simp only [pairIndicator,or_comm]

 def weightGraph (f : Tensor K ι) : SimpleGraph ι where
  Adj u v := u≠v ∧ f (pairIndicator u v)≠0
  symm := ⟨by intro u v h; exact ⟨h.1.symm,by simpa only [pairIndicator_comm v u] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

 theorem sameLift_pair (i j : ι) (p q : Remaining i j) :
    sameLift i j false (pairIndicator p q)=pairIndicator p.val q.val := by
  funext k
  by_cases hi : k=i
  · subst k
    simp [pairIndicator,Ne.symm p.property.1,Ne.symm q.property.1]
  · by_cases hj : k=j
    · subst k
      simp [pairIndicator,Ne.symm p.property.2,Ne.symm q.property.2]
    · simp [sameLift,hi,hj,pairIndicator,Subtype.ext_iff]

 theorem sameLift_false_zero (i j : ι) : sameLift i j false (fun _=>false)=(fun _=>false) := by
  funext k
  simp [sameLift]

 theorem sameLift_true_zero (i j : ι) : sameLift i j true (fun _=>false)=pairIndicator i j := by
  funext k
  by_cases hi : k=i <;> by_cases hj : k=j <;> simp [sameLift,pairIndicator,hi,hj]

 theorem card_add (f : Tensor K ι) (i j : ι) (y : Remaining i j → Bool) :
    card f i j false y+card f i j true y=4*f (sameLift i j false y) := by
  simp only [card,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul]
  ring

 theorem card_sub (f : Tensor K ι) (i j : ι) (y : Remaining i j → Bool) :
    card f i j false y-card f i j true y=4*f (sameLift i j true y) := by
  simp only [card,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul]
  ring

 theorem card_both_zero_iff (htwo : (2:K)≠0) (f : Tensor K ι) (i j : ι)
    (y : Remaining i j → Bool) :
    card f i j false y=0 ∧ card f i j true y=0 ↔
      f (sameLift i j false y)=0 ∧ f (sameLift i j true y)=0 := by
  have hfour : (4:K)≠0 := by convert mul_ne_zero htwo htwo using 1 <;> norm_num
  constructor
  · rintro ⟨hp,hm⟩
    have ha := card_add f i j y
    have hs := card_sub f i j y
    rw [hp,hm,add_zero] at ha
    rw [hp,hm,sub_zero] at hs
    exact ⟨(mul_eq_zero.mp ha.symm).resolve_left hfour,(mul_eq_zero.mp hs.symm).resolve_left hfour⟩
  · rintro ⟨hp,hm⟩
    simp [card,hp,hm]

 theorem first_slice_card_cover (htwo : (2:K)≠0) (f : Tensor K ι) (i j : ι)
    (y : Remaining i j → Bool) (hf : f (sameLift i j false y)≠0) :
    card f i j false y≠0 ∨ card f i j true y≠0 := by
  by_contra h
  push_neg at h
  exact hf ((card_both_zero_iff htwo f i j y).mp h).1

 theorem left_only_slice (f : Tensor K ι) (i j : ι)
    (y : Remaining i j → Bool) (hp : card f i j false y≠0) (hm : card f i j true y=0) :
    f (sameLift i j false y)≠0 := by
  intro hf
  have h := card_add f i j y
  rw [hf,mul_zero,hm,add_zero] at h
  exact hp h

 theorem right_only_slice (f : Tensor K ι) (i j : ι)
    (y : Remaining i j → Bool) (hm : card f i j true y≠0) (hp : card f i j false y=0) :
    f (sameLift i j false y)≠0 := by
  intro hf
  have h := card_add f i j y
  rw [hf,mul_zero,hp,zero_add] at h
  exact hm h

end Holant.ReedMuller.MatchingConsistency
