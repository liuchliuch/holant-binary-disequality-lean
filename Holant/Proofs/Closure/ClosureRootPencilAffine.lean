import Holant.Proofs.Closure.ClosureRootPencilProduct
import Holant.Proofs.Closure.ClosureRootPencilCount

/-! Literal affine pencil identities and zero-safe support bookkeeping.
No common matching, common parity plane or ruling is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective
open scoped BigOperators

def pencil (U V : Signature ℂ 4) (t : ℂ) : Signature ℂ 4 := fun x => U x + t * V x
def Dependent (U V : Signature ℂ 4) : Prop :=
  ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ a • U + b • V = 0
abbrev unionSupport (U V : Signature ℂ 4) : Finset Word :=
  ClosureRootPencilCount.unionSupport U V

theorem zero_sample_dependent {U V : Signature ℂ 4} {t : ℂ}
    (h : pencil U V t = 0) : Dependent U V := by
  refine ⟨1,t,Or.inl one_ne_zero,?_⟩
  funext x
  simpa only [pencil,Pi.add_apply,Pi.smul_apply,smul_eq_mul,one_mul] using congrFun h x

theorem independent_samples_nonzero {U V : Signature ℂ 4}
    (independent : ¬ Dependent U V) (t : ℂ) : pencil U V t ≠ 0 :=
  fun h => independent (zero_sample_dependent h)

theorem two_affine_zeros (a b s t : ℂ) (different : s ≠ t)
    (hs : a+s*b=0) (ht : a+t*b=0) : a=0 ∧ b=0 := by
  have hb : (s-t)*b=0 := by linear_combination hs-ht
  have bzero := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr different)
  exact ⟨by simpa [bzero] using hs,bzero⟩

theorem union_eq_two_samples (U V : Signature ℂ 4) (s t : ℂ) (different : s ≠ t) :
    unionSupport U V = support (pencil U V s) ∪ support (pencil U V t) := by
  classical
  ext x
  simp only [ClosureRootPencilCount.mem_unionSupport,Finset.mem_union,mem_support,pencil]
  constructor
  · intro active
    by_contra h
    push_neg at h
    have hz := two_affine_zeros (U x) (V x) s t different h.1 h.2
    exact active.elim (fun hn => hn hz.1) (fun hn => hn hz.2)
  · rintro (hn | hn)
    all_goals
      by_cases hu : U x = 0
      · right
        intro hv
        exact hn (by simp [hu,hv])
      · exact Or.inl hu

theorem combination (U V : Signature ℂ 4) (s t u : ℂ) (different : s ≠ t) :
    pencil U V u = ((t-u)/(t-s)) • pencil U V s +
      ((u-s)/(t-s)) • pencil U V t := by
  funext x
  change U x+u*V x = ((t-u)/(t-s))*(U x+s*V x)+((u-s)/(t-s))*(U x+t*V x)
  field_simp [sub_ne_zero.mpr different.symm]
  ring

@[simp] theorem complement_complement (x : Word) : complement (complement x)=x := by
  funext i
  simp [complement]

theorem complement_injective : Function.Injective complement := by
  intro x y h
  simpa using congrArg complement h

theorem complement_ne (x : Word) : complement x ≠ x := by
  intro h
  have h0 := congrFun h 0
  change (!(x 0)) = x 0 at h0
  cases hx : x 0 <;> simp [hx] at h0

/-- Word-complement pairing gives an even support cardinality, with all
actual words retained rather than quotiented into projective classes. -/
theorem closed_support_even (S : Finset Word)
    (closed : ∀ x ∈ S, complement x ∈ S) : Even S.card := by
  classical
  let left := S.filter (fun x => x 0 = false)
  let right := S.filter (fun x => x 0 = true)
  have image : left.image complement = right := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyS,hy0⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨closed y hyS,by simp [complement,hy0]⟩
    · intro hx
      obtain ⟨hxS,hx0⟩ := Finset.mem_filter.mp hx
      apply Finset.mem_image.mpr
      refine ⟨complement x,Finset.mem_filter.mpr ⟨closed x hxS,?_⟩,by simp⟩
      simp [complement,hx0]
  have equal : left.card=right.card := by
    rw [←image,Finset.card_image_of_injective _ complement_injective]
  have partition : left.card+right.card=S.card := by
    have h := Finset.card_filter_add_card_filter_not (s:=S) (fun x : Word => x 0=false)
    have other : S.filter (fun x => ¬ x 0=false) = right := by
      ext x
      simp only [Finset.mem_filter,right]
      cases hx : x 0 <;> simp [hx]
    simpa only [left,other] using h
  exact ⟨left.card,by omega⟩

theorem support_closed {m : ℕ} {q : Signature ℂ 4} (h : RootProduct m q) :
    ∀ x ∈ support q, complement x ∈ support q := by
  obtain ⟨D⟩ := h
  intro x hx
  exact (mem_support q _).mpr ((D.complement_supported x).mpr ((mem_support q x).mp hx))

theorem root_of_mem {m : ℕ} [NeZero m] {t : ℂ} (h : t ∈ Laurent.rootCoset m 1) : t^m=1 := by
  obtain ⟨u,hu⟩ := (Laurent.mem_rootCoset m 1 t).mp h
  have hr := u.property
  rw [mem_rootsOfUnity] at hr
  have hp := congrArg Units.val hr
  have hu' : (u.val : ℂ)=t := by simpa using hu
  simpa only [Units.val_pow_eq_pow_val,Units.val_one,hu'] using hp

theorem roots_two {m : ℕ} (hm : 2 ≤ m) :
    ∃ s t : ℂ, s^m=1 ∧ t^m=1 ∧ s≠t := by
  classical
  letI : NeZero m := ⟨by omega⟩
  have hcard : 1 < (Laurent.rootCoset m 1).card := by rw [Laurent.card_rootCoset];omega
  obtain ⟨s,hs,t,ht,different⟩ := Finset.one_lt_card.mp hcard
  exact ⟨s,t,root_of_mem hs,root_of_mem ht,different⟩

/-- Independent root samples have their actual four-point supports. -/
theorem independent_root_supports {m : ℕ} (U V : Signature ℂ 4)
    (independent : ¬ Dependent U V)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (t : ℂ) (ht : t^m=1) : RootProduct m (pencil U V t) :=
  (samples t ht).resolve_left (independent_samples_nonzero independent t)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
