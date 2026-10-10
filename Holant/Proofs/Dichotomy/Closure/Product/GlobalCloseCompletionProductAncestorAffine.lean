import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorSupport
import Holant.Tractable.SymmetricBinaryPullback.LocalAffine

/-! The genuine overlap between the Product and Affine classes for large
generalized equality components. Fourth-root endpoint ratios give one literal
affine formula at every arity. This is the class-selection rule required at
the exceptional native fourth-root marking. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionProductAncestorAffine
open Holant Holant.Tractable
open Holant.Tractable.SymmetricBinaryPullback
open GlobalCloseCompletionProductAncestorSupport
open scoped BigOperators

variable {n : ℕ}

def signedStarSystem (root : Fin n) (s : Fin n → Bool) : AffineSystem n where
  rows := n
  matrix i j := (if j = root then 1 else 0) + (if j = i then 1 else 0)
  rhs i := bitValue (ZMod 2) (s root) + bitValue (ZMod 2) (s i)

theorem signedStarSystem_holds (root : Fin n) (s x : Fin n → Bool) :
    (signedStarSystem root s).Holds x ↔ x = s ∨ x = fun i => !(s i) := by
  classical
  have bits : ∀ a b c d : Bool,
      bitValue (ZMod 2) a + bitValue (ZMod 2) b =
        bitValue (ZMod 2) c + bitValue (ZMod 2) d ↔
      (a ^^ c) = (b ^^ d) := by decide
  simp only [AffineSystem.Holds,signedStarSystem,add_mul,Finset.sum_add_distrib,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [bits]
  exact common_relative_iff root s x

theorem signed_star_affine (root : Fin n) (s : Fin n → Bool) :
    Affine (fun x : Fin n → Bool => if x = s ∨ x = (fun i => !(s i)) then 1 else 0) := by
  simpa only [signedStarSystem_holds] using affine_indicator (signedStarSystem root s)

theorem unary_of_equal_fourth_powers (root : Fin n) (a b : AlgebraicComplex)
    (ha : a ≠ 0) (equal : a^4 = b^4) :
    Affine (fun x : Fin n → Bool => if x root then b else a) := by
  have diagonal := affine_diagonal_of_fourth_power_eq a b ha equal
  have repeated := diagonal.precompose (fun x : Fin n → Bool => fun _ : Fin 2 => x root)
    (coordinates_isAffineMap (fun _ : Fin 2 => root))
  convert repeated using 1
  funext x
  cases h : x root <;> simp [kernelSignature,SymmetricBinaryPullback.diagonal,h]

/-- The full original coefficients are retained. No unary gadget or new
basis is asserted: the unary below is part of the literal affine formula. -/
theorem affine_of_support_pair_fourth_powers (f : Signature AlgebraicComplex n)
    (root : Fin n) (s : Fin n → Bool)
    (support : ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i))
    (first : f s ≠ 0) (second : f (fun i => !(s i)) ≠ 0)
    (equal : (f s)^4 = (f (fun i => !(s i)))^4) : Affine f := by
  classical
  have unary : Affine (fun x : Fin n → Bool =>
      if x root = s root then f s else f (fun i => !(s i))) := by
    cases hs : s root
    · convert unary_of_equal_fourth_powers root (f s) (f (fun i => !(s i))) first equal using 1 <;>
        funext x <;> cases x root <;> simp [hs]
    · convert unary_of_equal_fourth_powers root (f (fun i => !(s i))) (f s) second equal.symm using 1 <;>
        funext x <;> cases x root <;> simp [hs]
  have result := unary.mul (signed_star_affine root s)
  convert result using 1
  funext x
  by_cases left : x = s
  · subst x
    simp
  · by_cases right : x = fun i => !(s i)
    · subst x
      simp
    · have zero : f x = 0 := by
        by_contra live
        exact (support x live).elim left right
      simp [zero,left,right]

theorem affine_of_support_pair_root_four (f : Signature AlgebraicComplex n)
    (root : Fin n) (s : Fin n → Bool)
    (support : ∀ x, f x ≠ 0 → x = s ∨ x = fun i => !(s i))
    (first : f s ≠ 0) (second : f (fun i => !(s i)) ≠ 0)
    (ratio : (f s / f (fun i => !(s i)))^4 = 1) : Affine f := by
  apply affine_of_support_pair_fourth_powers f root s support first second
  rw [div_pow] at ratio
  exact (div_eq_one_iff_eq (pow_ne_zero 4 second)).mp ratio

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionProductAncestorAffine
end
