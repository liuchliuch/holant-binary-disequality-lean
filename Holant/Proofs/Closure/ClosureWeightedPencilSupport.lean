import Holant.Proofs.Closure.ClosureRootPencilRuling

/-! Four-port pencils with at least four root samples need only literal
nonsingular monomial product factors to have one support. Exponent zero in
Product records that support predicate without asserting a false phase ratio.
Zero samples and wholly zero pencils are retained. New proof, awaiting check. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Projective ClosureRootPencil

abbrev MonomialProduct (q : Signature ℂ 4) := RootProduct 0 q

def Samples (m : ℕ) (U V : Signature ℂ 4) : Prop :=
  ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ MonomialProduct (pencil U V t)

theorem another_root {m : ℕ} (hm : 2 ≤ m) (s : ℂ) :
    ∃ t : ℂ, t^m=1 ∧ s≠t := by
  obtain ⟨u,v,hu,hv,different⟩ := roots_two hm
  by_cases same : s=u
  · exact ⟨v,hv,by simpa only [same] using different⟩
  · exact ⟨u,hu,same⟩

theorem samples_union_le_four {m : ℕ} (hm : 4 ≤ m) (U V : Signature ℂ 4)
    (samples : Samples m U V) : (unionSupport U V).card ≤ 4 := by
  classical
  by_cases zeroSample : ∃ s : ℂ, s^m=1 ∧ pencil U V s=0
  · obtain ⟨s,hs,zero⟩ := zeroSample
    obtain ⟨t,ht,different⟩ := another_root (by omega : 2 ≤ m) s
    rw [union_eq_two_samples U V s t different]
    rcases samples t ht with zero' | actual
    · simp [zero,zero',support]
    · obtain ⟨D⟩ := actual
      have empty : support (0 : Signature ℂ 4)=∅ := by
        ext x
        simp [support]
      rw [zero,empty,Finset.empty_union]
      exact D.support_card.le
  · have live (t : ℂ) (ht : t^m=1) : pencil U V t≠0 :=
      fun zero => zeroSample ⟨t,ht,zero⟩
    have actual (t : ℂ) (ht : t^m=1) : MonomialProduct (pencil U V t) :=
      (samples t ht).resolve_left (live t ht)
    letI : NeZero m := ⟨by omega⟩
    have nonzero : ∀ t ∈ Laurent.rootCoset m 1, (fun x => U x+t*V x)≠0 :=
      fun t ht => live t (root_of_mem ht)
    have exactCard : ∀ t ∈ Laurent.rootCoset m 1,
        (ClosureRootPencilCount.pencilSupport U V t).card=4 := by
      intro t ht
      obtain ⟨D⟩ := actual t (root_of_mem ht)
      simpa only [ClosureRootPencilCount.pencilSupport,support,pencil] using D.support_card
    have bound := ClosureRootPencilCount.actual_roots_four_union_le_five m hm U V nonzero exactCard
    obtain ⟨s,t,hs,ht,different⟩ := roots_two (by omega : 2 ≤ m)
    have even : Even (unionSupport U V).card := by
      rw [union_eq_two_samples U V s t different]
      apply closed_support_even
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ (support_closed (actual s hs) x hx)
      · exact Finset.mem_union_right _ (support_closed (actual t ht) x hx)
    obtain ⟨k,hk⟩ := even
    change (unionSupport U V).card ≤ 5 at bound
    omega

theorem sampled_support_exact {m : ℕ} (hm : 4 ≤ m) (U V : Signature ℂ 4)
    (samples : Samples m U V) (t : ℂ) (ht : t^m=1) (live : pencil U V t≠0) :
    support (pencil U V t)=unionSupport U V := by
  classical
  obtain ⟨D⟩ := (samples t ht).resolve_left live
  apply Finset.eq_of_subset_of_card_le
  · exact ClosureRootPencilCount.pencilSupport_subset_union U V t
  · rw [D.support_card]
    exact samples_union_le_four hm U V samples

theorem exists_anchor {m : ℕ} (hm : 2 ≤ m) (U V : Signature ℂ 4)
    (nonzero : U≠0 ∨ V≠0) (samples : Samples m U V) :
    ∃ t : ℂ, t^m=1 ∧ MonomialProduct (pencil U V t) := by
  obtain ⟨s,t,hs,ht,different⟩ := roots_two hm
  by_cases zero : pencil U V s=0
  · have other : pencil U V t≠0 := by
      intro zero'
      have endpoints (x : Word) : U x=0 ∧ V x=0 :=
        two_affine_zeros (U x) (V x) s t different (congrFun zero x) (congrFun zero' x)
      have hu : U=0 := funext (fun x => (endpoints x).1)
      have hv : V=0 := funext (fun x => (endpoints x).2)
      exact nonzero.elim (fun h => h hu) (fun h => h hv)
    exact ⟨t,ht,(samples t ht).resolve_left other⟩
  · exact ⟨s,hs,(samples s hs).resolve_left zero⟩

theorem all_sampled_coordinate_det {m : ℕ} (hm : 4 ≤ m) (U V : Signature ℂ 4)
    (samples : Samples m U V) (t0 : ℂ) (ht0 : t0^m=1)
    (P : Product 0 (pencil U V t0)) (t : ℂ) (ht : t^m=1) :
    determinant (coordinates P (pencil U V t))=0 := by
  rcases samples t ht with zero | actual
  · simp only [zero,coordinates,determinant,Pi.zero_apply,zero_mul,sub_self]
  · obtain ⟨E⟩ := actual
    exact product_coordinates_det P E
      ((sampled_support_exact hm U V samples t0 ht0 P.nonzero_tensor).trans
        (sampled_support_exact hm U V samples t ht E.nonzero_tensor).symm).subset

theorem all_coordinates_span_det {m : ℕ} (hm : 4 ≤ m) (U V : Signature ℂ 4)
    (samples : Samples m U V) (t0 : ℂ) (ht0 : t0^m=1)
    (P : Product 0 (pencil U V t0)) (s t : ℂ) :
    determinant (s • coordinates P U+t • coordinates P V)=0 := by
  apply kernel_span_det (by omega : 3 ≤ m) _ _ _ s t
  intro z hz
  exact all_sampled_coordinate_det hm U V samples t0 ht0 P z hz

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
