import Holant.Proofs.Hardness.GeneralEOPhaseExtractionLoopTomography

/-! Algebraic rigidity of the order-two binary residual. Signed and unsigned
pair contractions recover complementary squares; unsigned contractions then
propagate one common complement sign through the nonzero support. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignLocal
open Holant
namespace F
export SelfDualPinObstruction (flip)
end F
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace T
export GeneralEOPhaseExtractionLoopTomography (merge merge_comp ext_of_merges merge_flip)
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
variable {n : ℕ}

def Square (f : Signature ℂ n) : Prop := ∀x,f (F.flip x)^2=f x^2

def Related (f : Signature ℂ n) (x y : Fin n→Bool) : Prop :=
  f (F.flip x)*f (F.flip y)=f x*f y

theorem sign_square (f : Signature ℂ n) (hf : S.Sign f) : Square f := by
  rcases hf with hf|hf
  · intro x
    rw [hf]
  · intro x
    rw [hf]
    ring

theorem sign_related (f : Signature ℂ n) (hf : S.Sign f) (x y : Fin n→Bool) :
    Related f x y := by
  rcases hf with hf|hf
  · simp only [Related,hf]
  · simp only [Related,hf,neg_mul_neg]

theorem square_zero (f : Signature ℂ n) (hf : Square f) (x : Fin n→Bool)
    (hx : f x=0) : f (F.flip x)=0 := by
  have hh := hf x
  rw [hx,zero_pow (by decide : (2:ℕ)≠0)] at hh
  exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp hh

theorem related_through (f : Signature ℂ n) (hf : Square f)
    (x y z : Fin n→Bool) (hz : f z≠0)
    (hxz : Related f x z) (hzy : Related f z y) : Related f x y := by
  apply mul_right_cancel₀ (pow_ne_zero 2 hz)
  calc
    _ = (f (F.flip x)*f (F.flip z))*(f (F.flip z)*f (F.flip y)) := by
      rw [←hf z]
      ring
    _ = (f x*f z)*(f z*f y) := by rw [hxz,hzy]
    _ = _ := by ring

theorem sign_of_related (f : Signature ℂ n)
    (hr : ∀x y,Related f x y) : S.Sign f := by
  classical
  by_cases hz : ∀x,f x=0
  · exact Or.inl (fun x=>by rw [hz,hz])
  push Not at hz
  obtain ⟨w,hw⟩ := hz
  have hs : (f (F.flip w))^2=(f w)^2 := by simpa only [Related,pow_two] using hr w w
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hp|hm
  · left
    intro x
    have hh := hr w x
    change f (F.flip w)*f (F.flip x)=f w*f x at hh
    rw [hp] at hh
    exact mul_left_cancel₀ hw hh
  · right
    intro x
    have hh := hr w x
    change f (F.flip w)*f (F.flip x)=f w*f x at hh
    rw [hm] at hh
    apply mul_left_cancel₀ hw
    linear_combination -hh

def signedMerge (f : Signature ℂ (n+2)) (e : Equiv.Perm (Fin (n+2))) : Signature ℂ n :=
  fun x=>f (O.word true false x ∘ e)-f (O.word false true x ∘ e)

theorem square_of_merges (f : Signature ℂ (n+3))
    (hE : Signature.CentralSupport f)
    (hp : ∀e,Square (T.merge f e)) (hm : ∀e,Square (signedMerge f e)) : Square f := by
  let g : Signature ℂ (n+3) := fun x=>f x^2
  have hg : Signature.CentralSupport g := by
    intro x hx
    simp only [g,hE x hx,zero_pow (by decide : (2:ℕ)≠0)]
  apply GeneralEOPhaseExtractionLoopTomography.selfDual_of_merges g hg
  intro e x
  have hplus := hp e x
  have hminus := hm e x
  change (f (O.word false true (F.flip x) ∘ e)+f (O.word true false (F.flip x) ∘ e))^2=
    (f (O.word false true x ∘ e)+f (O.word true false x ∘ e))^2 at hplus
  change (f (O.word true false (F.flip x) ∘ e)-f (O.word false true (F.flip x) ∘ e))^2=
    (f (O.word true false x ∘ e)-f (O.word false true x ∘ e))^2 at hminus
  change f (O.word false true (F.flip x) ∘ e)^2+f (O.word true false (F.flip x) ∘ e)^2=
    f (O.word false true x ∘ e)^2+f (O.word true false x ∘ e)^2
  linear_combination (1/2 : ℂ)*hplus+(1/2 : ℂ)*hminus

theorem related_adjacent (f : Signature ℂ (n+2)) (hf : Square f)
    (hm : Square (T.merge f (Equiv.refl _))) (x : Fin n→Bool) :
    Related f (O.word false true x) (O.word true false x) := by
  have hs := hm x
  have h0 := hf (O.word false true x)
  have h1 := hf (O.word true false x)
  simp only [T.merge,Equiv.coe_refl,Function.comp_id,S.flip_word,Bool.not_false,Bool.not_true]
    at hs h0 h1
  change f (F.flip (O.word false true x))*f (F.flip (O.word true false x))=
    f (O.word false true x)*f (O.word true false x)
  rw [S.flip_word,S.flip_word]
  simp only [Bool.not_false,Bool.not_true]
  linear_combination (1/2 : ℂ)*hs-(1/2 : ℂ)*h0-(1/2 : ℂ)*h1

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinarySignLocal
