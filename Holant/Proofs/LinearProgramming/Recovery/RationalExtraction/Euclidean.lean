import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Codec

set_option autoImplicit false

/-! Integer quotient/residual identities for the accelerated rational search. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction.DivMod

def jump (n k : ℕ) : ℕ := (n-1)/k
def residual (n k : ℕ) : ℕ := (n-1)%k+1

theorem split (n k : ℕ) (hn : 0<n) : n=jump n k*k+residual n k := by
  calc
    n=(n-1)+1 := by omega
    _=((n-1)%k+k*((n-1)/k))+1 :=
      congrArg (fun a : ℕ => a+1) (Nat.mod_add_div (n-1) k).symm
    _=jump n k*k+residual n k := by
      unfold jump residual
      ac_rfl
theorem residual_pos (n k : ℕ) : 0<residual n k := by unfold residual; omega
theorem residual_le (n k : ℕ) (hk : 0<k) : residual n k≤k := by
  have h := Nat.mod_lt (n-1) hk
  unfold residual
  omega
theorem jump_pos (n k : ℕ) (hk : 0<k) (hkn : k<n) : 0<jump n k := by
  exact Nat.div_pos (by omega) hk
theorem jump_le (n k : ℕ) : jump n k≤n :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)

/-- The two-branch Euclidean potential estimate needed by accelerated search.
It is independent of any promised answer and uses actual quotient residuals. -/
theorem two_jump_halves (n k m t : ℕ) (hn : 0<n) (hk : 0<k) (hkn : k<n)
    (hm : m=residual n k) (ht : 0<t) (hpos : 0<k-t*m) (hnext : k-t*m<m) :
    2*max m (k-t*m)≤n := by
  have hs := split n k hn
  have hj := jump_pos n k hk hkn
  have hr := residual_le n k hk
  rw [← hm] at hs hr
  have hmax : max m (k-t*m)=m := max_eq_left hnext.le
  rw [hmax]
  by_cases htwo : 2*k≤n
  · omega
  · have hjone : jump n k=1 := by
      by_contra h
      have hjtwo : 2≤jump n k := by omega
      have hmul := Nat.mul_le_mul_right k hjtwo
      omega
    rw [hjone,one_mul] at hs
    omega

end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction.DivMod
