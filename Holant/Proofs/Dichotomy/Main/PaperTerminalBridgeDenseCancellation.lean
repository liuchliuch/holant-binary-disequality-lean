import Holant.Proofs.Dichotomy.Retained.StableDenseParityAlgebra

/-! A finite exact diagonal cancellation choice for the no-I eight-vertex
source. Three rational parameters suffice to avoid both vanishing loci.
The algebraic diagonal actions are recorded explicitly; their physical access
must be supplied by the genuine no-I anti-diagonal interpolation programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseCancellation
open Holant Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem distinct_hits (a b x y : K) (ha : a≠0) (different : x≠y)
    (hx : a*x=b) (hy : a*y=b) : False :=
  different (mul_left_cancel₀ ha (hx.trans hy.symm))

theorem three_parameters (a b c d : K) (ha : a≠0) (hc : c≠0) :
    ∃t : K,(t=1 ∨ t=2 ∨ t=3) ∧ t≠0 ∧ a*t^2≠b ∧ c*t^2≠d := by
  classical
  by_cases one : a*1^2≠b ∧ c*1^2≠d
  · exact ⟨1,Or.inl rfl,one_ne_zero,one⟩
  by_cases two : a*2^2≠b ∧ c*2^2≠d
  · exact ⟨2,Or.inr (Or.inl rfl),by norm_num,two⟩
  have oneFail : a*1^2=b ∨ c*1^2=d := by
    by_cases h : a*1^2=b
    · exact Or.inl h
    · exact Or.inr (by by_contra hC;exact one ⟨h,hC⟩)
  have twoFail : a*2^2=b ∨ c*2^2=d := by
    by_cases h : a*2^2=b
    · exact Or.inl h
    · exact Or.inr (by by_contra hC;exact two ⟨h,hC⟩)
  refine ⟨3,Or.inr (Or.inr rfl),by norm_num,?_⟩
  rcases oneFail with h1|h1 <;> rcases twoFail with h2|h2
  · exact (distinct_hits a b (1^2) (2^2) ha (by norm_num) h1 h2).elim
  · exact ⟨fun h3=>distinct_hits a b (1^2) (3^2) ha (by norm_num) h1 h3,
      fun h3=>distinct_hits c d (2^2) (3^2) hc (by norm_num) h2 h3⟩
  · exact ⟨fun h3=>distinct_hits a b (2^2) (3^2) ha (by norm_num) h2 h3,
      fun h3=>distinct_hits c d (1^2) (3^2) hc (by norm_num) h1 h3⟩
  · exact (distinct_hits c d (1^2) (2^2) hc (by norm_num) h1 h2).elim

def dress (f : Signature K 4) (r t : K) : Signature K 4 :=
  fun x=>(if x 0 then r else 1)*(if x 1 then t else 1)*f x

theorem entries_dress (f : Signature K 4) (r t : K) :
    entries (dress f r t)=⟨(entries f).a,(entries f).b,t*(entries f).c,t*(entries f).d,
      r*(entries f).w,r*(entries f).z,r*t*(entries f).y,r*t*(entries f).x⟩ := by
  apply Entries.ext <;> simp [dress,entries]

theorem even_dress (f : Signature K 4) (even : EvenSupport f) (r t : K) : EvenSupport (dress f r t) := by
  intro x odd
  simp only [dress,even x odd,mul_zero]

theorem cancellation (f : Signature K 4) (even : EvenSupport f)
    (dense : StableDenseParityAlgebra.Dense f)
    (separate : (entries f).a*(entries f).x≠(entries f).b*(entries f).y) :
    ∃t : K,(t=1 ∨ t=2 ∨ t=3) ∧ t≠0 ∧
      (-(entries f).b/((entries f).y*t))≠0 ∧
      EightVertexCancellationLocal.Applicable (dress f (-(entries f).b/((entries f).y*t)) t) := by
  let e := entries f
  rcases dense with ⟨ha,hb,hc,hd,hw,hz,hy,hx⟩
  change e.y≠0 at hy
  obtain ⟨t,choice,ht,sum,additional⟩ := three_parameters (e.d*e.y) (e.b*e.w)
    (e.d^2*e.y) (e.b*e.c*e.z) (mul_ne_zero hd hy) (mul_ne_zero (pow_ne_zero 2 hd) hy)
  let r := -e.b/(e.y*t)
  have hr : r≠0 := div_ne_zero (neg_ne_zero.mpr hb) (mul_ne_zero hy ht)
  refine ⟨t,choice,ht,hr,?_⟩
  have cancel : e.b+r*t*e.y=0 := by dsimp [r];field_simp [hy,ht];ring
  have outer : e.a*(r*t*e.x)+e.b^2≠0 := by
    have value : e.a*(r*t*e.x)+e.b^2=(-e.b/e.y)*(e.a*e.x-e.b*e.y) := by
      dsimp [r];field_simp [hy,ht];ring
    rw [value]
    exact mul_ne_zero (div_ne_zero (neg_ne_zero.mpr hb) hy) (sub_ne_zero.mpr separate)
  have sumValue : e.y*t*(r*e.w+t*e.d)=e.d*e.y*t^2-e.b*e.w := by
    dsimp [r];field_simp [hy,ht];ring
  have liveSum : r*e.w+t*e.d≠0 := by
    intro zero
    have h := congrArg (fun z=>e.y*t*z) zero
    rw [sumValue,mul_zero] at h
    exact sum (sub_eq_zero.mp h)
  have additionalValue : e.y*((t*e.c)*(r*e.z)+(t*e.d)^2)=e.d^2*e.y*t^2-e.b*e.c*e.z := by
    dsimp [r];field_simp [hy,ht];ring
  have liveAdditional : (t*e.c)*(r*e.z)+(t*e.d)^2≠0 := by
    intro zero
    have h := congrArg (fun z=>e.y*z) zero
    rw [additionalValue,mul_zero] at h
    exact additional (sub_eq_zero.mp h)
  refine ⟨even_dress f even r t,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [entries_dress]
  · exact cancel
  · exact outer
  · exact mul_ne_zero ht hc
  · exact mul_ne_zero hr hz
  · exact liveSum
  · exact Or.inl liveAdditional


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseCancellation
end
