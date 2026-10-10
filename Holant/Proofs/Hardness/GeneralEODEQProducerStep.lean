import Holant.Proofs.Hardness.GeneralEODEQProducerCore

/-! An isolated supported interval is preserved by literal paired pinning.
Once the interval fills the boundary, native self-loops reduce its arity
without cancellation. Every coefficient of its two endpoints is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerStep
open Holant Holant.Complexity FixedGadgetSubstitution
open GeneralEODEQProducerCore
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

private theorem tail_eq {u v u' v' : Bool} {a b : Fin n → Bool}
    (h : O.word u v a=O.word u' v' b) : a=b := by
  funext i
  exact congrFun h i.succ.succ

private theorem prefix_ne (a b : Fin n → Bool) :
    O.word false true a≠O.word true false b := by
  intro h
  have hh := congrFun h 0
  exact Bool.false_ne_true hh

def pinnedPair (S : Network K (n+2)) (p : Pair S.denote) (a b : Fin n → Bool)
    (ha : p.left=O.word false true a) (hb : p.right=O.word false true b) :
    Pair (O.pinned S false).denote where
  left := a
  right := b
  left_supported := by simpa only [O.pinned_denote,Bool.not_false,←ha] using p.left_supported
  right_supported := by simpa only [O.pinned_denote,Bool.not_false,←hb] using p.right_supported
  distant := by
    have h := p.distant
    rw [ha,hb,D.distance_word] at h
    simpa only [ite_true,Nat.zero_add] using h
  isolated := by
    intro x hx hfix
    rw [O.pinned_denote] at hx
    have hs := p.isolated (O.word false true x) hx
    have hi : ∀i,p.left i=p.right i → O.word false true x i=p.left i := by
      rw [ha,hb]
      intro i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
      · intro _; rfl
      · intro _; rfl
      · exact hfix i
    rcases hs hi with h | h
    · exact Or.inl (tail_eq (h.trans ha))
    · exact Or.inr (tail_eq (h.trans hb))

def loop (S : Network K (n+2)) : Network K n := S.contract Signature.disequality

theorem loop_denote (S : Network K (n+2)) (x : Fin n → Bool) :
    (loop S).denote x=S.denote (O.word false true x)+S.denote (O.word true false x) :=
  Network.denote_contract_disequality S x

theorem loop_central (S : Network K (n+2)) (he : Signature.CentralSupport S.denote) :
    Signature.CentralSupport (loop S).denote := by
  intro x hx
  rw [loop_denote]
  have h01 : S.denote (O.word false true x)=0 := by
    apply he
    rw [O.word_weight]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega
  have h10 : S.denote (O.word true false x)=0 := by
    apply he
    rw [O.word_weight]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega
  simp only [h01,h10,add_zero]

theorem only_endpoints (S : Network K n) (p : Pair S.denote)
    (hm : D.distance p.left p.right=n) :
    ∀x,S.denote x≠0 → x=p.left ∨ x=p.right := by
  intro x hx
  apply p.isolated x hx
  intro i hi
  exact False.elim ((distance_eq_iff p.left p.right).mp hm i hi)

def loopPair (S : Network K (n+2)) (p : Pair S.denote) (a b : Fin n → Bool)
    (ha : p.left=O.word false true a) (hb : p.right=O.word true false b)
    (hm : D.distance p.left p.right=n+2) (hd : 4≤D.distance a b) :
    Pair (loop S).denote := by
  have hab : a≠b := by
    rintro rfl
    simp only [D.distance_self] at hd
    omega
  have hcrossA : S.denote (O.word true false a)=0 := by
    by_contra hh
    rcases only_endpoints S p hm _ hh with h | h
    · exact prefix_ne a a (h.trans ha).symm
    · exact hab (tail_eq (h.trans hb))
  have hcrossB : S.denote (O.word false true b)=0 := by
    by_contra hh
    rcases only_endpoints S p hm _ hh with h | h
    · exact hab (tail_eq (h.trans ha)).symm
    · exact prefix_ne b b (h.trans hb)
  refine ⟨a,b,?_,?_,hd,?_⟩
  · simpa only [loop_denote,hcrossA,add_zero,←ha] using p.left_supported
  · simpa only [loop_denote,hcrossB,zero_add,←hb] using p.right_supported
  · intro x hx _
    rw [loop_denote] at hx
    by_cases h : S.denote (O.word false true x)=0
    · have hn : S.denote (O.word true false x)≠0 := by simpa only [h,zero_add] using hx
      rcases only_endpoints S p hm _ hn with hh | hh
      · exact Or.inl (tail_eq (hh.trans ha))
      · exact Or.inr (tail_eq (hh.trans hb))
    · rcases only_endpoints S p hm _ h with hh | hh
      · exact Or.inl (tail_eq (hh.trans ha))
      · exact Or.inr (tail_eq (hh.trans hb))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerStep
