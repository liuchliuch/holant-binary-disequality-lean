import Holant.ReedMuller.AffineRadon.Phase
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Exact nonzero loci of the signed quadratic-phase orbit numerators. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem imaginary_bracket_ne_zero : (1+imaginaryUnit : AlgebraicComplex)≠0 ∧
    (1-imaginaryUnit : AlgebraicComplex)≠0 := by
  have h : (1+imaginaryUnit)*(1-imaginaryUnit)=(2 : AlgebraicComplex) := by
    linear_combination -imaginaryUnit_sq
  have hn : (1+imaginaryUnit)*(1-imaginaryUnit)≠(0 : AlgebraicComplex) := by
    rw [h]
    norm_num
  exact mul_ne_zero_iff.mp hn

/-- All scalar cancellations, including both real constant phases and both
imaginary constant phases. -/
theorem phase_bracket_nonzero_iff (α : ZMod 4) (b : ZMod 2) :
    (1+fourthRootPhase α*phaseSign b : AlgebraicComplex)≠0 ↔
      α=1 ∨ α=3 ∨ (α=0 ∧ b=0) ∨ (α=2 ∧ b=1) := by
  obtain ⟨hp,hm⟩ := imaginary_bracket_ne_zero
  have hm' : (1+-imaginaryUnit : AlgebraicComplex)≠0 := by
    simpa only [sub_eq_add_neg] using hm
  rcases TwoTranslate.fourth_cases α with rfl | rfl | rfl | rfl <;>
    rcases TwoTranslate.binary_cases b with rfl | rfl <;>
    norm_num [show (1 : ZMod 2)+1=0 from rfl,hp,hm',sub_eq_add_neg] <;> decide

/-- One derivative from `Q` gives the exact plus/minus support equations. -/
theorem phaseValue_signed_support (c : AlgebraicComplex) (hc : c≠0)
    (a : BinaryVector n) (U : BinaryCode n) (Q : QuadraticPhase n)
    (s : BinaryVector n) (hs : s∈U) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2, ∀ b x,
      (phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)≠0) ↔
        x-a∈U ∧ (α=1 ∨ α=3 ∨ (α=0 ∧ ell x=b) ∨ (α=2 ∧ ell x=b+1)) := by
  obtain ⟨α,ell,h⟩ := phaseValue_signed_factor c hc a U Q s hs
  refine ⟨α,ell,?_⟩
  intro b x
  rw [h,mul_ne_zero_iff,phaseValue_ne_zero_iff c hc,phase_bracket_nonzero_iff]
  have hz : ∀ b d : ZMod 2, b+d=0 ↔ d=b := by decide
  have ho : ∀ b d : ZMod 2, b+d=1 ↔ d=b+1 := by decide
  rw [hz,ho]

/-- The actual ambient direction of a binary level set inside the support. -/
def phaseKernel (U : BinaryCode n) (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) :
    BinaryCode n := U ⊓ LinearMap.ker ell

@[simp] theorem mem_phaseKernel (U : BinaryCode n) (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2)
    (x : BinaryVector n) : x∈phaseKernel U ell ↔ x∈U ∧ ell x=0 := Iff.rfl

/-- Every nonempty binary level set is literally a translate of the kernel
intersection, in the original ambient coordinates. -/
theorem phase_level_translate (a y : BinaryVector n) (U : BinaryCode n)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (t : ZMod 2)
    (hy : y-a∈U) (hyt : ell y=t) (x : BinaryVector n) :
    (x-a∈U ∧ ell x=t) ↔ x-y∈phaseKernel U ell := by
  rw [mem_phaseKernel,map_sub,hyt,sub_eq_zero]
  have he : x-a=(x-y)+(y-a) := by abel
  rw [he,U.add_mem_iff_left hy]

/-- Constant restrictions give exactly the empty or full support alternative. -/
theorem phase_level_constant (a : BinaryVector n) (U : BinaryCode n)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (h : ell.comp U.subtype=0)
    (x : BinaryVector n) (hx : x-a∈U) : ell x=ell a := by
  have hv := congrArg (fun L : U →ₗ[ZMod 2] ZMod 2 => L ⟨x-a,hx⟩) h
  simp only [LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.zero_apply,map_sub] at hv
  exact sub_eq_zero.mp hv

/-- Nonconstant binary restrictions are onto, so both affine level sets exist. -/
theorem phase_level_exists (a : BinaryVector n) (U : BinaryCode n)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (h : ell.comp U.subtype≠0) (t : ZMod 2) :
    ∃ y : BinaryVector n, y-a∈U ∧ ell y=t := by
  obtain ⟨u,hu⟩ := LinearMap.surjective h (t-ell a)
  refine ⟨a+u,?_,?_⟩
  · simpa using u.property
  · change ell u=t-ell a at hu
    rw [map_add,hu]
    abel

/-- A nonconstant restriction cuts the support direction by exactly one
 dimension; the direction here is the actual ambient intersection. -/
theorem phaseKernel_finrank (U : BinaryCode n)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (h : ell.comp U.subtype≠0) :
    Module.finrank (ZMod 2) (phaseKernel U ell)+1=Module.finrank (ZMod 2) U := by
  have he : LinearMap.ker (ell.comp U.subtype)=
      (phaseKernel U ell).comap U.subtype := by
    ext x
    simp [phaseKernel]
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero h
  rw [he,(Submodule.comapSubtypeEquivOfLe (show phaseKernel U ell≤U from inf_le_left)).finrank_eq]
    at hd
  exact hd

/-- Exact empty, full, and genuine affine-hyperplane alternatives. -/
theorem phase_level_trichotomy (a : BinaryVector n) (U : BinaryCode n)
    (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) (t : ZMod 2) :
    (∀ x, x-a∈U → ell x≠t) ∨
    (∀ x, x-a∈U → ell x=t) ∨
    (∃ y : BinaryVector n, y-a∈U ∧ ell y=t ∧
      Module.finrank (ZMod 2) (phaseKernel U ell)+1=Module.finrank (ZMod 2) U ∧
      ∀ x, (x-a∈U ∧ ell x=t) ↔ x-y∈phaseKernel U ell) := by
  classical
  by_cases h : ell.comp U.subtype=0
  · by_cases ht : ell a=t
    · exact Or.inr (Or.inl (fun x hx => (phase_level_constant a U ell h x hx).trans ht))
    · exact Or.inl (fun x hx => by rw [phase_level_constant a U ell h x hx]; exact ht)
  · obtain ⟨y,hy,hyt⟩ := phase_level_exists a U ell h t
    exact Or.inr (Or.inr ⟨y,hy,hyt,phaseKernel_finrank U ell h,
      phase_level_translate a y U ell t hy hyt⟩)

/-- Both signed numerators have translation-invariant nonzero loci. -/
theorem signed_numerator_translate (g : BinaryVector n → AlgebraicComplex)
    (s x : BinaryVector n) (b : ZMod 2) :
    g (x+s)+phaseSign b*g (x+s+s)=
      phaseSign b*(g x+phaseSign b*g (x+s)) := by
  have hss : s+s=0 := by funext i; exact CharTwo.add_self_eq_zero (s i)
  rw [add_assoc,hss,add_zero]
  have hb := phaseSign_square b
  linear_combination -(g (x+s))*hb

/-- The cancellation alternatives derived from the genuine quadratic phase.
A proper locus is an actual affine hyperplane inside `a+U`, with its ambient
code, exact codimension, and translation direction retained. -/
theorem phaseValue_signed_locus (c : AlgebraicComplex) (hc : c≠0)
    (a : BinaryVector n) (U : BinaryCode n) (Q : QuadraticPhase n)
    (s : BinaryVector n) (hs : s∈U) (b : ZMod 2) :
    (∀ x, phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)=0) ∨
    (∀ x, (phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)≠0) ↔ x-a∈U) ∨
    (∃ (y : BinaryVector n) (D : BinaryCode n), y-a∈U ∧ D≤U ∧ s∈D ∧
      Module.finrank (ZMod 2) D+1=Module.finrank (ZMod 2) U ∧
      ∀ x, (phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)≠0) ↔ x-y∈D) := by
  classical
  let N := fun x => phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)
  obtain ⟨α,ell,h⟩ := phaseValue_signed_support c hc a U Q s hs
  have hlevel (t : ZMod 2) (he : ∀ x, N x≠0 ↔ x-a∈U ∧ ell x=t) :
      (∀ x, N x=0) ∨ (∀ x, N x≠0 ↔ x-a∈U) ∨
      (∃ (y : BinaryVector n) (D : BinaryCode n), y-a∈U ∧ D≤U ∧ s∈D ∧
        Module.finrank (ZMod 2) D+1=Module.finrank (ZMod 2) U ∧
        ∀ x, N x≠0 ↔ x-y∈D) := by
    rcases phase_level_trichotomy a U ell t with hz | hf | ⟨y,hy,hyt,hd,hyD⟩
    · left
      intro x
      by_contra hx
      obtain ⟨hxU,hxt⟩ := (he x).mp hx
      exact hz x hxU hxt
    · right;left
      intro x
      rw [he]
      exact ⟨And.left,fun hx => ⟨hx,hf x hx⟩⟩
    · have heD (x) : N x≠0 ↔ x-y∈phaseKernel U ell := (he x).trans (hyD x)
      have hyN : N y≠0 := (he y).mpr ⟨hy,hyt⟩
      have hsN : N (y+s)≠0 := by
        change phaseValue c a U Q (y+s)+phaseSign b*phaseValue c a U Q (y+s+s)≠0
        rw [signed_numerator_translate]
        exact mul_ne_zero (fun hb => by simpa [hb] using phaseSign_square b) hyN
      have hsD : s∈phaseKernel U ell := by
        simpa only [add_sub_cancel_left] using (heD (y+s)).mp hsN
      exact Or.inr (Or.inr ⟨y,phaseKernel U ell,hy,inf_le_left,hsD,hd,heD⟩)
  rcases TwoTranslate.fourth_cases α with rfl | rfl | rfl | rfl
  · apply hlevel b
    intro x
    simpa only [N,show (0 : ZMod 4)≠1 from by decide,
      show (0 : ZMod 4)≠3 from by decide,show (0 : ZMod 4)≠2 from by decide,
      false_or,false_and,or_false,true_and] using h b x
  · right;left
    intro x
    simpa only [show (1 : ZMod 4)=1 from rfl,true_or,and_true] using h b x
  · apply hlevel (b+1)
    intro x
    simpa only [N,show (2 : ZMod 4)≠1 from by decide,
      show (2 : ZMod 4)≠3 from by decide,show (2 : ZMod 4)≠0 from by decide,
      false_or,false_and,true_and] using h b x
  · right;left
    intro x
    simpa only [show (3 : ZMod 4)=3 from rfl,true_or,or_true,and_true] using h b x

/-- When the derivative's binary part is constant on the affine support,
the exact bracket is a single scalar. It vanishes precisely when its
fourth-root ratio is `-1`; otherwise the entire support survives. -/
theorem phaseValue_constant_phase_alternative (c : AlgebraicComplex) (hc : c≠0)
    (a : BinaryVector n) (U : BinaryCode n) (Q : QuadraticPhase n)
    (s : BinaryVector n) (hs : s∈U) :
    ∃ α : ZMod 4, ∃ ell : BinaryVector n →ₗ[ZMod 2] ZMod 2,
      (∀ b x, phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)=
        phaseValue c a U Q x*(1+fourthRootPhase α*phaseSign (b+ell x))) ∧
      (ell.comp U.subtype=0 → ∀ b,
        ((∀ x, phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)=0) ↔
          fourthRootPhase α*phaseSign (b+ell a)= -1) ∧
        (fourthRootPhase α*phaseSign (b+ell a)≠ -1 → ∀ x,
          (phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)≠0) ↔ x-a∈U)) := by
  classical
  obtain ⟨α,ell,h⟩ := phaseValue_signed_factor c hc a U Q s hs
  refine ⟨α,ell,h,?_⟩
  intro hconst b
  have he (x : BinaryVector n) :
      phaseValue c a U Q x+phaseSign b*phaseValue c a U Q (x+s)=
        phaseValue c a U Q x*(1+fourthRootPhase α*phaseSign (b+ell a)) := by
    rw [h]
    by_cases hx : x-a∈U
    · rw [phase_level_constant a U ell hconst x hx]
    · simp [phaseValue,hx]
  have ha : phaseValue c a U Q a≠0 :=
    (phaseValue_ne_zero_iff c hc a U Q a).mpr (by simp)
  have hbracket : (1+fourthRootPhase α*phaseSign (b+ell a)=0) ↔
      fourthRootPhase α*phaseSign (b+ell a)= -1 := by
    exact add_eq_zero_iff_eq_neg'
  constructor
  · constructor
    · intro hz
      have hz' := hz a
      rw [he] at hz'
      exact hbracket.mp ((mul_eq_zero.mp hz').resolve_left ha)
    · intro hz x
      rw [he,hbracket.mpr hz,mul_zero]
  · intro hn x
    rw [he,mul_ne_zero_iff,phaseValue_ne_zero_iff c hc]
    exact and_iff_left ((not_congr hbracket).mpr hn)

end
end Holant.ReedMuller.AffineRadon
