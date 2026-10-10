import Holant.Proofs.Hardness.GeneralEORootNormLocal

/-! Distance induction converts the three-phase norm identities into a common
conjugate-reversal scalar, retaining the actual unsigned child hypotheses. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormRigidity
open Holant
namespace L
export GeneralEORootNormLocal (NormSymmetry Related flip_zero ars_related related_through related_adjacent ars_of_related
  rootMerge norm_of_root_children ars_norm mass)
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

variable (t : Fin 3 → ℂ) (distinct : Function.Injective t) (unit : ∀ i, ‖t i‖ = 1)
include distinct unit

theorem related_of_children (n k : ℕ) : ∀f : Signature ℂ (n+2),
    Signature.CentralSupport f → L.NormSymmetry f →
    (∀e,GeneralEOARSBoundary.ARSUpToScale (T.merge f e)) →
    (∀e i,L.NormSymmetry (L.rootMerge f e (t i))) → ∀x y,D.distance x y=k → L.Related f x y := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro f hE hf hm hr x y hxy
    by_cases hx : f x=0
    · simp only [L.Related,hx,L.flip_zero f hf x hx,star_zero,zero_mul]
    by_cases hy : f y=0
    · simp only [L.Related,hy,L.flip_zero f hf y hy,star_zero,mul_zero]
    by_cases he : x=y
    · subst y
      simpa only [L.Related,L.mass,mul_comm] using hf x
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
    have hf' : L.NormSymmetry f' := fun z=>hf (z ∘ e.symm)
    have hm' (p : Equiv.Perm (Fin (n+2))) : GeneralEOARSBoundary.ARSUpToScale (T.merge f' p) :=
      hm (e.symm.trans p)
    have hr' (p : Equiv.Perm (Fin (n+2))) (i : Fin 3) :
        L.NormSymmetry (L.rootMerge f' p (t i)) := hr (e.symm.trans p) i
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
      exact L.related_adjacent t distinct unit f' (hr' (Equiv.refl _)) v
    have hpos := D.distance_pos huv
    by_cases hz : f' (O.word true false u)≠0
    · apply L.related_through f' hf' _ _ (O.word true false u) hz
      · apply ih (D.distance (O.word false true u) (O.word true false u)) ?_
          f' hE' hf' hm' hr' _ _ rfl
        simp only [D.distance_word,D.distance_self,Bool.false_eq_true,Bool.true_eq_false,
          ite_false] at hd ⊢
        omega
      · apply ih (D.distance (O.word true false u) (O.word true false v)) ?_
          f' hE' hf' hm' hr' _ _ rfl
        simp only [D.distance_word,Bool.false_eq_true,Bool.true_eq_false,
          ite_false,ite_true] at hd ⊢
        omega
    by_cases hw : f' (O.word false true v)≠0
    · apply L.related_through f' hf' _ _ (O.word false true v) hw
      · apply ih (D.distance (O.word false true u) (O.word false true v)) ?_
          f' hE' hf' hm' hr' _ _ rfl
        simp only [D.distance_word,Bool.false_eq_true,Bool.true_eq_false,
          ite_false,ite_true] at hd ⊢
        omega
      · apply ih (D.distance (O.word false true v) (O.word true false v)) ?_
          f' hE' hf' hm' hr' _ _ rfl
        simp only [D.distance_word,D.distance_self,Bool.false_eq_true,Bool.true_eq_false,
          ite_false] at hd ⊢
        omega
    have hz0 := not_ne_iff.mp hz
    have hw0 := not_ne_iff.mp hw
    have hzc := L.flip_zero f' hf' (O.word true false u) hz0
    have hwc := L.flip_zero f' hf' (O.word false true v) hw0
    simp only [S.flip_word,Bool.not_false,Bool.not_true] at hzc hwc
    have hc := L.ars_related _ (hm' (Equiv.refl _)) u v
    simp only [L.Related,T.merge,Equiv.refl_apply,Function.comp_def,hz0,hw0,hzc,hwc,
      zero_add,add_zero] at hc
    simpa only [L.Related,S.flip_word,Bool.not_false,Bool.not_true] using hc

theorem ars_of_children {n : ℕ} (f : Signature ℂ (n+3))
    (hE : Signature.CentralSupport f)
    (hm : ∀e,GeneralEOARSBoundary.ARSUpToScale (T.merge f e))
    (hr : ∀e i,L.NormSymmetry (L.rootMerge f e (t i))) :
    GeneralEOARSBoundary.ARSUpToScale f := by
  have hf := L.norm_of_root_children t distinct unit f hE hr
  apply L.ars_of_related f hf
  intro x y
  exact related_of_children t distinct unit (n+1) (D.distance x y) f hE hf hm hr x y rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEORootNormRigidity
