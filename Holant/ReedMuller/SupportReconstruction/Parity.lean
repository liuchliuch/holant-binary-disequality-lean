import Holant.ReedMuller.SupportReconstruction.Ratio
import Holant.ReedMuller.SupportReconstruction.SliceCode

/-! Literal inversion of the two actual card equations selects the unique
parity lift, including zero coefficients and both signs. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.WeightTwoIntegration Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open scoped BigOperators
variable {r : ℕ}

 def parity (t : Fin r → Bool) : ZMod 2 := ∑e,vectorWord t e

 theorem sign_finite_sum {E : Type*} (s : Finset E) (f : E → ZMod 2) :
    sign (∑e∈s,f e)=∏e∈s,sign (f e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih => simp [he,sign_add,ih]

 theorem parity_sign (t : Fin r → Bool) :
    (∏e,(-1:ℂ)^(if t e then 1 else 0 : ℕ))=sign (parity t) := by
  rw [parity,sign_finite_sum]
  apply Finset.prod_congr rfl
  intro e _
  cases ht : t e <;> simp [vectorWord,ht,boolEquiv]

 theorem invert_parity (a b c : ℂ) (s : ZMod 2)
    (hp : 2*(a+b)=c) (hm : 2*(a-b)=sign s*c) :
    a=(if s=0 then c/2 else 0) ∧ b=(if s=0 then 0 else c/2) := by
  rcases (by decide : ∀s : ZMod 2,s=0 ∨ s=1) s with rfl | rfl
  · simp only [sign_zero,one_mul] at hm
    simp only [ite_true]
    constructor
    · linear_combination hp/4+hm/4
    · linear_combination hp/4-hm/4
  · simp only [sign_one,neg_one_mul] at hm
    simp only [show (1:ZMod 2)≠0 from by decide,ite_false]
    constructor
    · linear_combination hp/4+hm/4
    · linear_combination hp/4-hm/4

 theorem invert_parity_nonzero (a b c : ℂ) (hc : c≠0) (s : ZMod 2)
    (hp : 2*(a+b)=c) (hm : 2*(a-b)=sign s*c) (z : Bool) :
    (if z then b else a)≠0 ↔ boolEquiv z=s := by
  obtain ⟨ha,hb⟩ := invert_parity a b c s hp hm
  rw [ha,hb]
  have hd : c/2≠0 := div_ne_zero hc (by norm_num)
  rcases (by decide : ∀s : ZMod 2,s=0 ∨ s=1) s with rfl | rfl <;>
    cases z <;> simp [boolEquiv,hd]

 namespace MatchingCards
 variable {ι : Type*} [DecidableEq ι] {f : Tensor ℂ ι} {i j : ι} (D : MatchingCards f i j)

 theorem selected_lift (hW : weightGraph f=⊥) (t : Fin D.plus.edges → Bool) (b : Bool) :
    f (sameLift i j b (logicalWord D.plus t))≠0 ↔ boolEquiv b=parity t := by
  let a := f (sameLift i j false (logicalWord D.plus t))
  let c := f (sameLift i j true (logicalWord D.plus t))
  have hp : 2*(a+c)=D.plus.value (logicalWord D.plus t) := by
    have hh := congrFun D.plus_eq (logicalWord D.plus t)
    simpa [card,a,c] using hh
  have hm : 2*(a-c)=sign (parity t)*D.plus.value (logicalWord D.plus t) := by
    have hh := congrFun D.minus_eq (logicalWord D.plus t)
    rw [D.minus_parity (by norm_num) hW,parity_sign] at hh
    simpa [card,a,c,sub_eq_add_neg] using hh
  have hh := invert_parity_nonzero a c _ (logical_supported D.plus t) (parity t) hp hm b
  cases b <;> exact hh

 theorem logical_reconstruct (y : ZeroCardGraph.Remaining i j → Bool) (hy : D.plus.value y≠0) :
    logicalWord D.plus (fun e=>y (D.plus.ports (e,false)))=y := by
  funext p
  obtain ⟨⟨e,b⟩,rfl⟩ := D.plus.ports.surjective p
  rw [logical_port]
  cases b
  · rfl
  · exact (D.plus.value_nonzero_iff y).mp hy e

 theorem matching_of_lift (b : Bool) (y : ZeroCardGraph.Remaining i j → Bool)
    (hy : f (sameLift i j b y)≠0) : D.plus.value y≠0 := by
  by_contra hp
  have hq : D.minus.value y=0 := by
    by_contra hq
    have hs := (D.minus.support_spec y).mp hq
    have hpne : D.plus.value y≠0 := by
      apply (D.plus.support_spec y).mpr
      change ∀p,y ((Pairing.ofPorts D.plus.ports).mate p)=y p
      rw [D.matching]
      exact hs
    exact hpne hp
  have hh := (card_both_zero_iff (by norm_num : (2:ℂ)≠0) f i j y).mp (by
    rw [D.plus_eq,D.minus_eq]; exact ⟨hp,hq⟩)
  cases b
  · exact hy hh.1
  · exact hy hh.2

 end MatchingCards
end Holant.ReedMuller.SupportReconstruction
