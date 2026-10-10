import Holant.Proofs.Closure.ClosureRootPencilSegre
import Holant.Proofs.Closure.ClosureSixPortProportionalSupport

/-! Zero-safe whole-pencil Segre equations. The genuine dependent support
bound is combined with the checked independent bound, so no sampled zero or
proportional pencil is discarded and no common support is an input. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective Polynomial

theorem sampled_support_exact {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (t : ℂ) (ht : t^m=1) (nonzero : pencil U V t≠0) :
    support (pencil U V t)=unionSupport U V := by
  classical
  obtain ⟨D⟩ := (samples t ht).resolve_left nonzero
  apply Finset.eq_of_subset_of_card_le
  · exact ClosureRootPencilCount.pencilSupport_subset_union U V t
  · rw [D.support_card]
    exact ClosureSixPort.Proportional.samples_union_le_four hm U V samples

theorem exists_root_anchor {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (nonzero : U≠0 ∨ V≠0)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    ∃ t : ℂ, t^m=1 ∧ RootProduct m (pencil U V t) := by
  obtain ⟨s,t,hs,ht,different⟩ := roots_two (by omega : 2 ≤ m)
  by_cases hzero : pencil U V s=0
  · have other : pencil U V t≠0 := by
      intro h
      have zeros (x : Word) : U x=0 ∧ V x=0 :=
        two_affine_zeros (U x) (V x) s t different (congrFun hzero x) (congrFun h x)
      have hu : U=0 := funext (fun x => (zeros x).1)
      have hv : V=0 := funext (fun x => (zeros x).2)
      exact nonzero.elim (fun hn => hn hu) (fun hn => hn hv)
    exact ⟨t,ht,(samples t ht).resolve_left other⟩
  · exact ⟨s,hs,(samples s hs).resolve_left hzero⟩

theorem all_sampled_coordinate_det {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (t0 : ℂ) (ht0 : t0^m=1) (P : Product m (pencil U V t0))
    (t : ℂ) (ht : t^m=1) : determinant (coordinates P (pencil U V t))=0 := by
  rcases samples t ht with zero | actual
  · simp only [zero,coordinates,determinant,Pi.zero_apply,zero_mul,sub_self]
  · obtain ⟨E⟩ := actual
    apply product_coordinates_det P E
    exact ((sampled_support_exact hm U V samples t0 ht0 P.nonzero_tensor).trans
      (sampled_support_exact hm U V samples t ht E.nonzero_tensor).symm).subset

/-- A homogeneous determinant identity is derived by quadratic interpolation
on the actual root grid, including every sampled zero. -/
theorem kernel_span_det {m : ℕ} (hm : 3 ≤ m) (A B : Kernel ℂ)
    (samples : ∀ z : ℂ, z^m=1 → determinant (binaryPencil A B z)=0)
    (s t : ℂ) : determinant (s • A+t • B)=0 := by
  let mixed := A false false*B true true+B false false*A true true-
    A false true*B true false-B false true*A true false
  let poly : ℂ[X] :=
    (C (A false false)+C (B false false)*X)*(C (A true true)+C (B true true)*X)-
    (C (A false true)+C (B false true)*X)*(C (A true false)+C (B true false)*X)
  have linearDegree (a b : ℂ) : (C a+C b*X : ℂ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa using natDegree_C_mul_X_pow_le b 1
  have polyZero : poly=0 := by
    apply quadratic_eq_zero_on_rootPolygon hm
    · apply (natDegree_sub_le _ _).trans
      apply max_le <;> apply natDegree_mul_le.trans
      all_goals have := linearDegree (A false false) (B false false)
      all_goals have := linearDegree (A true true) (B true true)
      all_goals have := linearDegree (A false true) (B false true)
      all_goals have := linearDegree (A true false) (B true false)
      all_goals omega
    · intro z hz
      have he := samples z hz
      simp only [binaryPencil,determinant,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at he
      simp only [poly,eval_sub,eval_mul,eval_add,eval_C,eval_X]
      linear_combination he
  have expanded : poly=C (determinant A)+C mixed*X+C (determinant B)*X^2 := by
    dsimp [poly,determinant,mixed]
    simp only [map_add,map_sub,map_mul]
    ring
  have c0 := congrArg (fun q : ℂ[X] => q.coeff 0) polyZero
  have c1 := congrArg (fun q : ℂ[X] => q.coeff 1) polyZero
  have c2 := congrArg (fun q : ℂ[X] => q.coeff 2) polyZero
  have h0 : determinant A=0 := by simpa [expanded] using c0
  have h1 : mixed=0 := by simpa [expanded] using c1
  have h2 : determinant B=0 := by simpa [expanded] using c2
  have expansion : determinant (s • A+t • B)=
      s^2*determinant A+s*t*mixed+t^2*determinant B := by
    simp only [determinant,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    dsimp [mixed]
    ring
  rw [expansion,h0,h1,h2]
  ring

theorem all_coordinates_span_det {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t))
    (t0 : ℂ) (ht0 : t0^m=1) (P : Product m (pencil U V t0))
    (s t : ℂ) : determinant (s • coordinates P U+t • coordinates P V)=0 := by
  apply kernel_span_det hm _ _ _ s t
  intro z hz
  have he := all_sampled_coordinate_det hm U V samples t0 ht0 P z hz
  exact he

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
