import Holant.Proofs.Hardness.BinaryThreeSupportStarGraph
import Holant.Complexity.BinaryInterpolation.CommonDenominator

/-! Division-free common numerators for exact signed-star interpolation.
There is one final nonzero denominator. All node, numerator and denominator
factors are explicit powers, sums and products of original-field integers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarCommon
open Holant.Complexity.BinaryInterpolation
open scoped BigOperators
namespace S
export BinaryThreeSupportStars
  (polynomial polynomial_natDegree_le sample sample_exact signed signed_exact nodes_injective)
end S
namespace G
export BinaryThreeSupportStarGraph (base bits signed_eq expand_value)
end G
namespace R
export BinaryThreeSupportGraph (Raw value)
end R
namespace W
export BinaryCSPProgrammeStars (expand)
end W
variable {K : Type*} [Field K] [CharZero K]

def node {m : ℕ} (i : Fin (m+1)) : K := 2^i.val
def divisor {m : ℕ} (i : Fin (m+1)) : K := ∏j∈Finset.univ.erase i,(node i-node j)
def numerator {m : ℕ} (i : Fin (m+1)) : K := ∏j∈Finset.univ.erase i,((-1 : K)-node j)

theorem node_injective (m : ℕ) : Function.Injective (node (K:=K) (m:=m)) := by
  intro i j h
  apply Fin.ext
  exact S.nodes_injective h

theorem divisor_ne_zero {m : ℕ} (i : Fin (m+1)) : divisor (K:=K) i≠0 := by
  unfold divisor
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (fun h=>(Finset.mem_erase.mp hj).1 ((node_injective m h).symm))

theorem common_ne_zero (m : ℕ) : commonDenominator (divisor (K:=K) (m:=m))≠0 :=
  commonDenominator_ne_zero _ divisor_ne_zero

theorem basis_eval {m : ℕ} (i : Fin (m+1)) :
    (Lagrange.basis Finset.univ (node (K:=K)) i).eval (-1)=numerator i/divisor i := by
  simp only [Lagrange.basis,Lagrange.basisDivisor,Polynomial.eval_prod,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X,Finset.prod_mul_distrib]
  simp only [numerator,divisor,div_eq_mul_inv,Finset.prod_inv_distrib]
  exact mul_comm _ _

variable {A : Type*} [Fintype A] {m : ℕ}

theorem signed_common (base : A→K) (bits : A→Fin m→Bool) :
    S.signed base bits=(-1 : K)^m *
      (commonNumerator (divisor (K:=K) (m:=m))
        (fun i=>S.sample base bits i.val*numerator i) /
      commonDenominator (divisor (K:=K) (m:=m))) := by
  rw [S.signed_exact]
  congr 1
  have hd : (S.polynomial base bits).degree<((Finset.univ : Finset (Fin (m+1))).card : ℕ) := by
    rw [Finset.card_univ,Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (by
      exact_mod_cast (lt_of_le_of_lt (S.polynomial_natDegree_le base bits) (Nat.lt_succ_self m)))
  have hi := Lagrange.eq_interpolate (s:=(Finset.univ : Finset (Fin (m+1))))
    (v:=node (K:=K)) (node_injective m).injOn hd
  rw [hi,Lagrange.interpolate_apply,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,basis_eval]
  have he (i : Fin (m+1)) :
      (S.polynomial base bits).eval (node i) * (numerator i/divisor i)=
        (S.sample base bits i.val*numerator i)/divisor i := by
    rw [S.sample_exact]
    simp only [node,div_eq_mul_inv,mul_assoc]
  simp_rw [he]
  exact sum_div_common _ _ divisor_ne_zero

/-- The formula consumed by the physical common-denominator postprocessor.
Its only oracle values are the exact unsigned star graphs. -/
theorem graph_signed_common (r : R.Raw) (hr : r.WellFormed) :
    R.value (K:=K) r=(-1 : K)^r.signs.length *
      (commonNumerator (divisor (K:=K) (m:=r.signs.length))
        (fun i=>R.value (K:=K) (W.expand r i.val)*numerator i) /
      commonDenominator (divisor (K:=K) (m:=r.signs.length))) := by
  rw [G.signed_eq,signed_common]
  simp_rw [G.expand_value r hr]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportStarCommon
