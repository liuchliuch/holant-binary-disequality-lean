import Holant.Proofs.Closure.ClosureSourceRowsC2Deck

/-! Exact two-kernel reconstruction underlying the separate C2 higher-arity
analysis. Pair sums are the literal I/X contractions evaluated on a fixed
residual word. Three overlapping pairs determine every coefficient, so no
nonzero tensor can disappear under all of those contractions. This does not
assert the remaining higher matching-factor theorem or terminal hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2ContractionReconstruction
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false
variable {I K : Type*} [DecidableEq I] [CommRing K]

def flip (w : I→Bool) (i j : I) : I→Bool :=
  fun t=>w t ^^ (decide (t=i) ^^ decide (t=j))

theorem flip_flip (w : I→Bool) (i j k : I) :
    flip (flip w i j) j k=flip w i k := by
  funext t
  by_cases hi : t=i <;> by_cases hj : t=j <;> by_cases hk : t=k <;>
    cases hw : w t <;> simp [flip,hi,hj,hk,hw]

def pairSum (f : (I→Bool)→K) (i j : I) (w : I→Bool) : K := f w+f (flip w i j)

/-- No division and no characteristic restriction are needed for the exact
identity; repeated index parameters are permitted in this algebraic form. -/
theorem coefficient (f : (I→Bool)→K) (i j k : I) (w : I→Bool) :
    2*f w=pairSum f i j w+pairSum f i k w-pairSum f j k (flip w i j) := by
  simp only [pairSum,flip_flip]
  ring

variable [IsDomain K] [CharZero K]

/-- At least one real contraction among the three overlapping pairs is live.
Physical applications choose distinct indices to retain the pair interpretation. -/
theorem live_pair (f : (I→Bool)→K) (i j k : I) (w : I→Bool) (live : f w≠0) :
    pairSum f i j w≠0 ∨ pairSum f i k w≠0 ∨ pairSum f j k (flip w i j)≠0 := by
  by_contra absent
  push Not at absent
  have h := coefficient f i j k w
  rw [absent.1,absent.2.1,absent.2.2] at h
  exact mul_ne_zero (by norm_num : (2:K)≠0) live (by simpa using h)

/-- The common kernel of the six fixed I/X contraction maps is zero. -/
theorem zero_of_pair_sums (f : (I→Bool)→K) (i j k : I)
    (hij : ∀w,pairSum f i j w=0) (hik : ∀w,pairSum f i k w=0)
    (hjk : ∀w,pairSum f j k w=0) : f=0 := by
  funext w
  have h := coefficient f i j k w
  rw [hij,hik,hjk] at h
  simpa using h

/-- Bit complementation commutes with the actual two-port flip. -/
theorem flip_not (w : I → Bool) (i j : I) :
    flip (fun t => !w t) i j = fun t => !(flip w i j t) := by
  funext t
  by_cases hi : t = i <;> by_cases hj : t = j <;>
    cases hw : w t <;> simp [flip, hi, hj, hw]

/-- Complement invariance of the six contraction cards forces complement
invariance of the original tensor, with no parity or factorization premise. -/
theorem complement_of_pair_sums (f : (I → Bool) → K) (i j k : I)
    (hij : ∀ w, pairSum f i j w = pairSum f i j (fun t => !w t))
    (hik : ∀ w, pairSum f i k w = pairSum f i k (fun t => !w t))
    (hjk : ∀ w, pairSum f j k w = pairSum f j k (fun t => !w t)) :
    ∀ w, f w = f (fun t => !w t) := by
  intro w
  apply mul_left_cancel₀ (by norm_num : (2 : K) ≠ 0)
  rw [coefficient f i j k w, coefficient f i j k (fun t => !w t)]
  rw [hij w, hik w, hjk (flip w i j), flip_not]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2ContractionReconstruction
end
