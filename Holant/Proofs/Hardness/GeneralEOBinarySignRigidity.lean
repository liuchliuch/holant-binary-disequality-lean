import Holant.Proofs.Hardness.GeneralEOBinarySignLocal

/-! Distance induction converts the order-two pointwise condition into one
common complement sign, retaining the unsigned contraction hypotheses. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignRigidity
open Holant
namespace L
export GeneralEOBinarySignLocal (Square Related square_zero sign_square sign_related
  related_through related_adjacent sign_of_related)
end L
namespace F
export SelfDualPinObstruction (flip)
end F
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace T
export GeneralEOPhaseExtractionLoopTomography (merge merge_comp)
end T
namespace S
export GeneralEOPhaseExtractionSigns (Sign flip_word)
end S
namespace D
export GeneralEOPhaseExtractionDistance (distance distance_word distance_self distance_pos)
end D
namespace P
export GeneralEOPhaseExtractionCoordinates (opposite_prefix distance_comp)
end P
namespace E
export GeneralEOCentralHoleCoordinates (tail2 weight_comp)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem related_of_children (n k : ℕ) : ∀f : Signature ℂ (n+2),
    Signature.CentralSupport f → L.Square f →
    (∀e,S.Sign (T.merge f e)) → ∀x y,D.distance x y=k → L.Related f x y := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hE hf hm x y hxy
    by_cases hx : f x=0
    · simp only [L.Related,hx,L.square_zero f hf x hx,zero_mul]
    by_cases hy : f y=0
    · simp only [L.Related,hy,L.square_zero f hf y hy,mul_zero]
    by_cases he : x=y
    · subst y
      simpa only [L.Related,pow_two] using hf x
    have hwx : 2*weight x=n+2 := by
      by_contra h
      exact hx (hE x h)
    have hwy : 2*weight y=n+2 := by
      by_contra h
      exact hy (hE y h)
    obtain ⟨e,ex,ey⟩ := P.opposite_prefix x y (by omega) he
    let u := E.tail2 (x ∘ e)
    let v := E.tail2 (y ∘ e)
    let f' : Signature ℂ (n+2) := fun z=>f (z ∘ e.symm)
    have hE' : Signature.CentralSupport f' := by
      intro z hz
      apply hE
      simpa only [E.weight_comp] using hz
    have hf' : L.Square f' := fun z=>hf (z ∘ e.symm)
    have hm' (p : Equiv.Perm (Fin (n+2))) : S.Sign (T.merge f' p) :=
      hm (e.symm.trans p)
    have hd : D.distance (O.word false true u) (O.word true false v)=k := by
      rw [←ex,←ey,P.distance_comp,hxy]
    have transfer : L.Related f' (O.word false true u) (O.word true false v) →
        L.Related f x y := by
      rw [←ex,←ey]
      simp only [L.Related,f',F.flip,Function.comp_def,Equiv.apply_symm_apply]
      exact fun h=>h
    apply transfer
    by_cases huv : u=v
    · rw [huv]
      exact L.related_adjacent f' hf' (L.sign_square _ (hm' (Equiv.refl _))) v
    have hpos := D.distance_pos huv
    by_cases hz : f' (O.word true false u)≠0
    · apply L.related_through f' hf' _ _ (O.word true false u) hz
      · apply ih (D.distance (O.word false true u) (O.word true false u)) ?_
          f' hE' hf' hm' _ _ rfl
        simp only [D.distance_word,D.distance_self,Bool.false_eq_true,Bool.true_eq_false,
          ite_false] at hd ⊢
        omega
      · apply ih (D.distance (O.word true false u) (O.word true false v)) ?_
          f' hE' hf' hm' _ _ rfl
        simp only [D.distance_word,Bool.false_eq_true,Bool.true_eq_false,
          ite_false,ite_true] at hd ⊢
        omega
    by_cases hw : f' (O.word false true v)≠0
    · apply L.related_through f' hf' _ _ (O.word false true v) hw
      · apply ih (D.distance (O.word false true u) (O.word false true v)) ?_
          f' hE' hf' hm' _ _ rfl
        simp only [D.distance_word,Bool.false_eq_true,Bool.true_eq_false,
          ite_false,ite_true] at hd ⊢
        omega
      · apply ih (D.distance (O.word false true v) (O.word true false v)) ?_
          f' hE' hf' hm' _ _ rfl
        simp only [D.distance_word,D.distance_self,Bool.false_eq_true,Bool.true_eq_false,
          ite_false] at hd ⊢
        omega
    have hz0 := not_ne_iff.mp hz
    have hw0 := not_ne_iff.mp hw
    have hzc := L.square_zero f' hf' (O.word true false u) hz0
    have hwc := L.square_zero f' hf' (O.word false true v) hw0
    simp only [S.flip_word,Bool.not_false,Bool.not_true] at hzc hwc
    have hc := L.sign_related _ (hm' (Equiv.refl _)) u v
    simp only [L.Related,T.merge,Equiv.refl_apply,Function.comp_def,hz0,hw0,hzc,hwc,
      zero_add,add_zero] at hc
    simpa only [L.Related,S.flip_word,Bool.not_false,Bool.not_true] using hc

theorem sign_of_children {n : ℕ} (f : Signature ℂ (n+2))
    (hE : Signature.CentralSupport f) (hf : L.Square f)
    (hm : ∀e,S.Sign (T.merge f e)) : S.Sign f := by
  apply L.sign_of_related
  intro x y
  exact related_of_children n (D.distance x y) f hE hf hm x y rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignRigidity
