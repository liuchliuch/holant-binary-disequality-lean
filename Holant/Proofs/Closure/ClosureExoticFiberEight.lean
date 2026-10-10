import Holant.Proofs.Closure.ClosureExoticFiberCrossConstant
import Holant.Proofs.Closure.ClosureExoticFiberFlip
import Holant.Proofs.Closure.ClosureExoticOrientation

/-! Both literal cross orientations exclude a nonfactor exotic fibre with at
least four matching edges. No affine-permutation normal form is assumed. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Pauli.ExoticKlein
variable {P : Type*} [Fintype P] [LinearOrder P] {r : ℕ}

private theorem three_other_edges (hr : 4≤r) (u : Fin r) :
    ∃ v e f : Fin r,u≠v ∧ u≠e ∧ u≠f ∧ v≠e ∧ v≠f ∧ e≠f := by
  let i0 : Fin r := ⟨0,by omega⟩
  let i1 : Fin r := ⟨1,by omega⟩
  let i2 : Fin r := ⟨2,by omega⟩
  let i3 : Fin r := ⟨3,by omega⟩
  let s := Equiv.swap u i0
  have h0 : s i0=u := Equiv.swap_apply_right _ _
  have neq (i j : Fin r) (hij : i.val≠j.val) : s i≠s j :=
    fun h => hij (congrArg Fin.val (s.injective h))
  refine ⟨s i3,s i1,s i2,?_,?_,?_,?_,?_,?_⟩
  · rw [←h0];exact neq _ _ (by norm_num [i0,i1,i2,i3])
  · rw [←h0];exact neq _ _ (by norm_num [i0,i1,i2,i3])
  · rw [←h0];exact neq _ _ (by norm_num [i0,i1,i2,i3])
  · exact neq _ _ (by norm_num [i0,i1,i2,i3])
  · exact neq _ _ (by norm_num [i0,i1,i2,i3])
  · exact neq _ _ (by norm_num [i0,i1,i2,i3])

/-- A genuine ≥8-port PairSafe common fibre has a proper factor. Two actual
cross directions force both A+B and theta(A)+B constant, contradicting the
surjectivity of the same live label map A. -/
theorem eight_fibre_factor (M : Matching P r) (hr : 4≤r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label)
    (u : Fin r) (hlabel : ∀ a,labels a u=a)
    (hn : Fiber.tensor M weight labels≠0)
    (hs : MatchingCard.PairSafe (Fiber.tensor M weight labels)) :
    Fiber.HasProperTensorFactor (Fiber.tensor M weight labels) := by
  classical
  by_contra hnf
  have live := all_live M (by omega) weight labels u hlabel hn hs hnf
  have injective (d : Fin r) : Function.Injective (fun a => labels a d) :=
    fun a b h => labels_injective_on_live M (by omega) weight labels u hlabel hn hs hnf
      d a b (live a) (live b) h
  obtain ⟨v,e,f,huv,hue,huf,hve,hvf,hef⟩ := three_other_edges hr u
  have normal := cross_sum_constant M weight labels u v e f huv hue huf hve hvf hef
    hlabel live (injective v) hs
  have equation := flip_fiber M weight labels e
  have flippedSafe : MatchingCard.PairSafe
      (Fiber.tensor (flipped M e) (flipWeight weight labels e) (flipLabels labels e)) := equation ▸ hs
  have twisted := cross_sum_constant (flipped M e) (flipWeight weight labels e)
    (flipLabels labels e) u v e f huv hue huf hve hvf hef
    (flip_distinguished labels u e hue hlabel)
    (fun a => (flipWeight_live weight labels e a).mpr (live a))
    (flip_injective labels e v (injective v)) flippedSafe
  have twisted' : ∀ a b,theta (labels a e)+labels a f=theta (labels b e)+labels b f := by
    intro a b
    simpa only [flipLabels,ite_true,Ne.symm hef,ite_false] using twisted a b
  have surjective : Function.Surjective (fun a => labels a e) :=
    Finite.surjective_of_injective (injective e)
  rcases ClosureExoticOrientation.one_orientation_nonconstant
    (fun a => labels a e) (fun a => labels a f) surjective with ⟨a,b,h⟩ | ⟨a,b,h⟩
  · exact h (normal a b)
  · exact h (twisted' a b)

/-- All exotic OrderedPairSafe ancestors of even arity>=8 have a proper
factor, with the actual common fibre and all live/permutation data constructed. -/
theorem pair_safe_eight_factor (r : ℕ) (hr : 0<r) (f : Signature ℂ (2*r+6))
    (hf : f≠0) (hs : MatchingCard.OrderedPairSafe f) : Fiber.HasProperTensorFactor f := by
  obtain ⟨s,M,weight,labels,hlabel,he,hzero,hsz⟩ :=
    MatchingCard.common_full_fiber r hr f hf hs
  rw [he]
  exact eight_fibre_factor M (by omega) weight labels 0 hlabel (he ▸ hf)
    (he ▸ (MatchingCard.pairSafe_iff_ordered f).mpr hs)

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureExoticFiberCounts
