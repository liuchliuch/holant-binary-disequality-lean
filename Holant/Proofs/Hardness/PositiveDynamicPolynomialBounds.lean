import Holant.Proofs.Hardness.PositiveDynamicParameters

/-! Elementary size polynomials for a dynamic chain.  These are numerical
bounds for the eventual graph compiler, not a claim that it has been built. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicPolynomialBounds
variable (d : PositiveDynamicParameters.Data)

theorem block_size_le (m k : ℕ) (hk : k≤(m+1)^2) :
    d.length m*(k+1)≤2*d.constant*(m+1)^3 := by
  have h1 : 1≤(m+1)^2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have h2 : k+1≤2*(m+1)^2 := by omega
  calc
    d.length m*(k+1)≤d.length m*(2*(m+1)^2) := Nat.mul_le_mul_left _ h2
    _ =2*d.constant*(m+1)^3 := by simp [PositiveDynamicParameters.Data.length]; ring

/-- m positive-chain replacements, with k indexing the quadratic filter. -/
theorem replaced_size_le (m k : ℕ) (hk : k≤(m+1)^2) :
    m*(d.length m*(k+1))≤2*d.constant*(m+1)^4 := by
  calc
    m*(d.length m*(k+1))≤(m+1)*(2*d.constant*(m+1)^3) :=
      Nat.mul_le_mul (Nat.le_succ _) (block_size_le d m k hk)
    _ =2*d.constant*(m+1)^4 := by ring

/-- Add unchanged original-q rows separately; they are never retargeted. -/
theorem retained_plus_replaced_size_le (V m k : ℕ) (hk : k≤(m+1)^2) :
    V+m*(d.length m*(k+1))≤V+2*d.constant*(m+1)^4 :=
  Nat.add_le_add_left (replaced_size_le d m k hk) V

/-- A polynomial numerical envelope for all samples together. -/
theorem all_samples_size_le (V m k Q : ℕ) (hk : k≤(m+1)^2)
    (hQ : Q≤(m+1)^2+1) :
    Q*(V+m*(d.length m*(k+1)))≤((m+1)^2+1)*(V+2*d.constant*(m+1)^4) :=
  Nat.mul_le_mul hQ (retained_plus_replaced_size_le d V m k hk)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicPolynomialBounds
