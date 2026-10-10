import Holant.Proofs.Closure.ClosureSixPortZero
import Holant.Proofs.Closure.ClosureRootPencilSupport
import Holant.Proofs.Closure.ClosureRootPencilSource

/-! Exact zero-safe support consequences for proportional endpoint sectors.
The union bound is derived from the actual ordered root deck, including sampled
zeros and m=3. No common support, ruling, or factorization is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant Holant.Projective
namespace Proportional
open ClosureRootPencil

theorem nonzero_line_sample {m : ℕ} (hm : 2 ≤ m) (c : ℂ) :
    ∃ t : ℂ, t^m=1 ∧ 1+t*c ≠ 0 := by
  obtain ⟨s,t,hs,ht,different⟩ := roots_two hm
  by_cases h : 1+s*c=0
  · refine ⟨t,ht,?_⟩
    intro h'
    exact one_ne_zero (two_affine_zeros 1 c s t different h h').1
  · exact ⟨s,hs,h⟩

theorem line_pencil (U : Signature ℂ 4) (c t : ℂ) :
    pencil U (c • U) t = (1+t*c) • U := by
  funext x
  simp only [pencil,Pi.smul_apply,smul_eq_mul]
  ring

theorem support_scale (U : Signature ℂ 4) (c : ℂ) (nonzero : c ≠ 0) :
    support (c • U)=support U := by
  classical
  ext x
  simp [mem_support,Pi.smul_apply,smul_eq_mul,nonzero]

theorem union_line (U : Signature ℂ 4) (c : ℂ) :
    unionSupport U (c • U)=support U := by
  classical
  ext x
  simp only [ClosureRootPencilCount.mem_unionSupport,mem_support,
    Pi.smul_apply,smul_eq_mul]
  constructor
  · rintro (h | h)
    · exact h
    · exact (mul_ne_zero_iff.mp h).2
  · exact Or.inl

theorem dependent_endpoints_union_le_four {m : ℕ} (hm : 2 ≤ m)
    (U V : Signature ℂ 4) (dependent : DependentEndpoints U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    (unionSupport U V).card ≤ 4 := by
  classical
  rcases dependent with ⟨c,rfl⟩ | ⟨c,rfl⟩
  · obtain ⟨t,ht,coefficient⟩ := nonzero_line_sample hm c
    rw [union_line]
    rcases samples t ht with zero | actual
    · have Uzero : U=0 := by
        funext x
        have hz := congrFun zero x
        rw [line_pencil] at hz
        exact (mul_eq_zero.mp hz).resolve_left coefficient
      simp [Uzero,support]
    · obtain ⟨D⟩ := actual
      have card := D.support_card
      rw [line_pencil,support_scale U (1+t*c) coefficient] at card
      exact card.le
  · obtain ⟨s,t,hs,ht,different⟩ := roots_two hm
    have sample : ∃ t : ℂ, t^m=1 ∧ c+t ≠ 0 := by
      by_cases h : c+s=0
      · refine ⟨t,ht,?_⟩
        intro h'
        have both := two_affine_zeros c 1 s t different (by simpa using h) (by simpa using h')
        exact one_ne_zero both.2
      · exact ⟨s,hs,h⟩
    obtain ⟨t,ht,coefficient⟩ := sample
    have eq : pencil (c • V) V t = (c+t) • V := by
      funext x
      simp only [pencil,Pi.smul_apply,smul_eq_mul]
      ring
    have union : unionSupport (c • V) V=support V := by
      ext x
      simp only [ClosureRootPencilCount.mem_unionSupport,mem_support,
        Pi.smul_apply,smul_eq_mul]
      constructor
      · rintro (h | h)
        · exact (mul_ne_zero_iff.mp h).2
        · exact h
      · exact Or.inr
    rw [union]
    rcases samples t ht with zero | actual
    · have Vzero : V=0 := by
        funext x
        have hz := congrFun zero x
        rw [eq] at hz
        exact (mul_eq_zero.mp hz).resolve_left coefficient
      simp [Vzero,support]
    · obtain ⟨D⟩ := actual
      have card := D.support_card
      rw [eq,support_scale V (c+t) coefficient] at card
      exact card.le

theorem dependent_to_endpoints (U V : Signature ℂ 4) (dependent : Dependent U V) :
    DependentEndpoints U V := by
  obtain ⟨a,b,nonzero,equation⟩ := dependent
  by_cases hb : b=0
  · have ha : a ≠ 0 := nonzero.resolve_right (by simpa [hb])
    right
    refine ⟨0,?_⟩
    funext x
    have eq := congrFun equation x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,hb,
      zero_mul,add_zero] at eq
    simp only [Pi.smul_apply,smul_eq_mul,zero_mul]
    exact (mul_eq_zero.mp eq).resolve_left ha
  · left
    refine ⟨-(a/b),?_⟩
    funext x
    have eq := congrFun equation x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] at eq
    simp only [Pi.smul_apply,smul_eq_mul]
    field_simp
    linear_combination eq

/-- Whole four-port union bound, with all sampled zero cases retained. -/
theorem samples_union_le_four {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    (unionSupport U V).card ≤ 4 := by
  by_cases dependent : Dependent U V
  · exact dependent_endpoints_union_le_four (by omega) U V
      (dependent_to_endpoints U V dependent) samples
  · exact independent_union_le_four hm U V dependent samples

end Proportional

/-- Every actual sector's two analytic endpoint supports have at most four
words. This includes proportional, wholly zero and independent sectors. -/
theorem endpoint_union_le_four {m : ℕ} (hm : 3 ≤ m) (h : Signature ℂ 6)
    (deck : OrderedRootDeck m h) (e : Equiv.Perm (Fin 6)) (p : Bool) :
    (ClosureRootPencil.unionSupport (sliceSix h e p false) (sliceSix h e p true)).card ≤ 4 := by
  let U := sliceSix h e p false
  let V := sliceSix h e p true
  have samples : ∀ t : ℂ, t^m=1 → ClosureRootPencil.pencil U V t=0 ∨
      ClosureRootPencil.RootProduct m (ClosureRootPencil.pencil U V t) := by
    intro t ht
    have eq : ClosureRootPencil.pencil U V t=phaseCard h e p t := rfl
    rw [eq]
    exact (deck e p t ht).imp_right (ClosureRootPencil.rootMatching_iff_product m _).mp
  exact Proportional.samples_union_le_four hm U V samples

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
