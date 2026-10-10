import Holant.Complexity.BinaryInterpolation.AlgebraicSource.Roots
import Holant.Complexity.BinaryInterpolation.NormalizedQueries

/-! A genuinely algebraic, nonzero rank-one pencil is derived from an arbitrary
nonsingular infinite-order transfer. The mode records precisely geometric
(distinct-root) or positive-natural (Jordan) sampling. -/
namespace Holant.Complexity.BinaryInterpolation.AlgebraicSource
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Pencil (B : Binary (K := ℂ)) where
  H : Binary (K := ℂ)
  L : Binary (K := ℂ)
  beta : ℂ
  rho : ℂ
  geometric : Bool
  H_nonzero : H ≠ 0
  H_rank : H.rank = 1
  H_algebraic : EntriesAlgebraic H
  L_algebraic : EntriesAlgebraic L
  beta_algebraic : IsAlgebraic ℚ beta
  rho_algebraic : IsAlgebraic ℚ rho
  beta_nonzero : beta ≠ 0
  rho_nonzero : rho ≠ 0
  geometric_infinite : geometric = true → ∀ r : ℕ, 0 < r → rho^r ≠ 1
  jordan_left : geometric = false → L = X
  power_identity : ∀ t : ℕ, (B*X)^t*X =
    beta^t • (L + (if geometric then rho^t else (t:ℂ)) • H)

namespace Pencil
variable {B : Binary (K := ℂ)} (p : Pencil B)

def node (t : ℕ) : ℂ := if p.geometric then p.rho^t else (t:ℂ)

theorem node_algebraic (t : ℕ) : IsAlgebraic ℚ (p.node t) := by
  unfold node
  split_ifs
  · exact p.rho_algebraic.pow t
  · exact isAlgebraic_natCast t

theorem positive_nodes_injective (m : ℕ) :
    Function.Injective (fun i : Fin (m+1) => p.node (i.val+1)) := by
  cases hg : p.geometric
  · simpa [node,hg] using positive_natural_nodes_injective (K:=ℂ) m
  · simpa [node,hg] using geometric_nodes_injective (m:=m) p.rho p.rho_nonzero
      (p.geometric_infinite hg)

theorem normalization_nonzero (t m : ℕ) : p.beta^(t*m) ≠ 0 :=
  pow_ne_zero _ p.beta_nonzero

theorem normalization_algebraic (t m : ℕ) : IsAlgebraic ℚ (p.beta^(t*m)) :=
  p.beta_algebraic.pow _
end Pencil

theorem exists_pencil (B : Binary (K := ℂ)) (hB : EntriesAlgebraic B)
    (hd : Matrix.det (B*X) ≠ 0) (hi : ¬ProjectivelyFinite (B*X)) :
    Nonempty (Pencil B) := by
  let A := B*X
  have hA : EntriesAlgebraic A := entries_mul hB entries_X
  obtain ⟨a,b,haa,hba,ht,hdet⟩ := algebraic_eigenpair A hA
  have ha : a≠0 := (mul_ne_zero_iff.mp (hdet ▸ hd)).1
  have hb : b≠0 := (mul_ne_zero_iff.mp (hdet ▸ hd)).2
  by_cases hab : a=b
  · subst b
    let N := nilpotentPart A a
    let H : Binary (K:=ℂ) := a⁻¹ • (N*X)
    have hn : N≠0 := nilpotentPart_nonzero A a ha hi
    have hnd : Matrix.det N=0 := nilpotentPart_det A a ht hdet
    have hH : H≠0 := smul_ne_zero (inv_ne_zero ha) (right_X_nonzero N hn)
    have hHd : Matrix.det H=0 := by
      dsimp only [H]
      rw [Matrix.det_smul,right_X_singular N hnd,mul_zero]
    refine ⟨{
      H := H, L := X, beta := a, rho := 1, geometric := false,
      H_nonzero := hH, H_rank := singular_binary_rank H hH hHd,
      H_algebraic := entries_smul haa.inv (entries_mul (entries_nilpotent hA haa) entries_X),
      L_algebraic := entries_X, beta_algebraic := haa, rho_algebraic := isAlgebraic_one,
      beta_nonzero := ha, rho_nonzero := one_ne_zero,
      geometric_infinite := (by intro h; cases h),
      jordan_left := (by intro; rfl),
      power_identity := ?_ }⟩
    intro t
    change A^t*X=a^t • (X+(t:ℂ) • H)
    rw [repeated_power A a ha ht hdet,Matrix.smul_mul,add_mul,Matrix.one_mul,
      Matrix.smul_mul,Matrix.smul_mul]
  · let P := spectralProjector A a b
    have hp : P≠0 := spectralProjector_nonzero A a b hab ht
    have hpd : Matrix.det P=0 := spectralProjector_determinant A a b ht hdet
    have hpa : EntriesAlgebraic P := entries_projector hA haa hba
    refine ⟨{
      H := P*X, L := (1-P)*X, beta := b, rho := a/b, geometric := true,
      H_nonzero := right_X_nonzero P hp,
      H_rank := singular_binary_rank _ (right_X_nonzero P hp) (right_X_singular P hpd),
      H_algebraic := entries_mul hpa entries_X,
      L_algebraic := entries_mul (entries_sub entries_one hpa) entries_X,
      beta_algebraic := hba, rho_algebraic := (by simpa only [div_eq_mul_inv] using haa.mul hba.inv),
      beta_nonzero := hb, rho_nonzero := div_ne_zero ha hb,
      geometric_infinite := (by intro; exact eigenratio_infinite A a b hab ha hb ht hdet hi),
      jordan_left := (by intro h; cases h),
      power_identity := ?_ }⟩
    intro t
    change A^t*X=b^t • ((1-P)*X+(a/b)^t • (P*X))
    rw [distinct_power A a b hab ht hdet,add_mul,Matrix.smul_mul,Matrix.smul_mul]
    change a^t • (P*X)+b^t • ((1-P)*X)=b^t • ((1-P)*X+(a/b)^t • (P*X))
    rw [smul_add,smul_smul]
    have he : b^t*(a/b)^t=a^t := by rw [div_pow]; field_simp
    rw [he]
    exact add_comm _ _

end
end Holant.Complexity.BinaryInterpolation.AlgebraicSource
