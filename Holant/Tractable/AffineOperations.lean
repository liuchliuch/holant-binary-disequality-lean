import Holant.Tractable.TwoTranslate
import Holant.Tensor

/-!
# Affine coordinate substitution and variable summation

All operations use the existing finite GF(2) support systems and even-mixed
Z/4 phases. Pulling a support back by an affine Boolean map gives an explicitly
constructed system. Summing an actual Boolean coordinate follows from the
verified two-translate closure, without assuming Gaussian elimination or any
tractable-evaluation oracle. No runtime bound or free gadget resource is claimed.
-/

set_option backward.isDefEq.respectTransparency false

namespace Holant.Tractable
noncomputable section
open AffinePhase TwoTranslate

namespace AffineSystem

/-- Pull back every support equation along an affine Boolean coordinate map.
The coefficients are the map's actual differences at the coordinate basis. -/
def pullback {m n : ℕ} (S : AffineSystem n) (p : Word m → Word n) : AffineSystem m where
  rows := S.rows
  matrix r j := rowDot (S.matrix r) (p (basis j)) - rowDot (S.matrix r) (p (origin m))
  rhs r := S.rhs r - rowDot (S.matrix r) (p (origin m))

/-- Each pulled-back row is exactly the affine functional's linear part. -/
theorem pullback_row {m n : ℕ} (S : AffineSystem n) (p : Word m → Word n)
    (hp : IsAffineMap p) (r : Fin S.rows) (x : Word m) :
    rowDot ((S.pullback p).matrix r) x =
      rowDot (S.matrix r) (p x) - rowDot (S.matrix r) (p (origin m)) := by
  let q : Word m → ZMod 2 := fun y =>
    rowDot (S.matrix r) (p y) - rowDot (S.matrix r) (p (origin m))
  have hq0 : q (origin m) = 0 := by simp [q]
  have hq (y z : Word m) : q (xor y z) = q y + q z := by
    dsimp [q]
    rw [hp]
    simp only [rowDot_xor]
    ring_nf
    have h2 : (2 : ZMod 2) = 0 := by decide
    simp [h2]
  have heq : q = fun y => dot ((S.pullback p).matrix r) y :=
    additive_word_eq _ _ hq0 (by simp) hq
      (by intro y z; rw [dot_xor]) (by intro j; simp [dot_basis, q, pullback])
  exact (congrFun heq x).symm

/-- Pullback is a literal equivalence of the finite systems' solution predicates. -/
theorem pullback_holds {m n : ℕ} (S : AffineSystem n) (p : Word m → Word n)
    (hp : IsAffineMap p) (x : Word m) : (S.pullback p).Holds x ↔ S.Holds (p x) := by
  change (∀ r, rowDot ((S.pullback p).matrix r) x = (S.pullback p).rhs r) ↔
    (∀ r, rowDot (S.matrix r) (p x) = S.rhs r)
  apply forall_congr'
  intro r
  rw [pullback_row S p hp]
  change (_ - _ = _ - _) ↔ _
  exact sub_left_inj

end AffineSystem

/-- The actual affine class is closed under arbitrary affine Boolean substitutions,
including noninjective maps, constants, permutations, and changes of arity. -/
theorem Affine.precompose {m n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f)
    (p : Word m → Word n) (hp : IsAffineMap p) : Affine (fun x => f (p x)) := by
  rcases hf with rfl | ⟨s, hs, S, Q, rfl⟩
  · exact affine_zero m
  · convert ((affine_quadratic_precompose Q p hp).scale s).restrict (S.pullback p) using 1
    funext x
    simp only [affineFormula, AffineSystem.pullback_holds S p hp]

/-- Inserting a fixed first coordinate is an affine Boolean map. -/
theorem cons_isAffineMap {n : ℕ} (b : Bool) :
    IsAffineMap (fun x : Word n => Fin.cons b x) := by
  intro x y
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · cases b <;> rfl
  · simp [AffinePhase.xor, origin]

/-- Fixing an actual coordinate retains affinity; this is a semantic class closure,
not an assertion that a pinning signature is supplied to the Holant problem. -/
theorem Affine.pin_first {n : ℕ} {f : Signature AlgebraicComplex (n + 1)}
    (hf : Affine f) (b : Bool) : Affine (fun x => f (Fin.cons b x)) :=
  hf.precompose _ (cons_isAffineMap b)

/-- Summation over one actual Boolean variable preserves the source affine class.
The proof derives this operation from the full two-translate theorem. -/
theorem Affine.sum_first {n : ℕ} {f : Signature AlgebraicComplex (n + 1)}
    (hf : Affine f) : Affine (fun x => f (Fin.cons false x) + f (Fin.cons true x)) := by
  let w : Word (n + 1) := Fin.cons true (origin n)
  have h := (hf.two_translate w).pin_first false
  convert h using 1
  funext x
  congr 1
  congr 1
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rfl
  · simp [AffinePhase.xor, w, origin]

/-- Pointwise multiplication uses the intersection of actual support equations
and the sum of the two actual quadratic phases. -/
theorem Affine.mul {n : ℕ} {f g : Signature AlgebraicComplex n}
    (hf : Affine f) (hg : Affine g) : Affine (fun x => f x * g x) := by
  rcases hf with rfl | ⟨s, hs, S, Q, rfl⟩
  · left; funext x; simp
  rcases hg with rfl | ⟨t, ht, T, R, rfl⟩
  · left; funext x; simp
  have hp : Affine (fun x => fourthRootPhase (Q.eval x + R.eval x)) := by
    apply affine_phase_of_thirdDifference
    intro z u v w
    rw [thirdDifference_add, quadratic_thirdDifference, quadratic_thirdDifference, add_zero]
  convert (hp.scale (s * t)).restrict (S.inter T) using 1
  funext x
  by_cases hS : S.Holds x <;> by_cases hT : T.Holds x <;>
    simp [affineFormula, AffineSystem.inter_holds, hS, hT, fourthRootPhase_add, mul_assoc, mul_left_comm]

/-- Selecting and repeating coordinates is an affine Boolean substitution. -/
theorem coordinates_isAffineMap {m n : ℕ} (indices : Fin n → Fin m) :
    IsAffineMap (fun x : Word m => fun j => x (indices j)) := by
  intro x y
  funext j
  simp [AffinePhase.xor, origin]

/-- Bilinear contraction with an affine binary table preserves the actual affine
class. This is a class-closure identity, not a claim of gadget availability. -/
theorem Affine.contract {n : ℕ} {f : Signature AlgebraicComplex (n + 2)}
    (hf : Affine f) (E : Bool → Bool → AlgebraicComplex)
    (hE : Affine (fun x : Fin 2 → Bool => E (x 0) (x 1))) :
    Affine (Signature.contract E f) := by
  let indices : Fin 2 → Fin (n + 2) := ![0, 1]
  have hext : Affine (fun x : Word (n + 2) => E (x 0) (x 1)) :=
    hE.precompose (fun x j => x (indices j)) (coordinates_isAffineMap indices)
  have h := ((hext.mul hf).sum_first).sum_first
  convert h using 1
  funext x
  simp only [Signature.contract, Fintype.sum_bool, Fin.cons_zero]
  ac_rfl

end
end Holant.Tractable
