import Holant.ReedMuller.AffinePatching.BooleanLinear
import Holant.Tractable.AffineOperations
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection

/-! Recover actual affine equations and an affine retraction from ternary
closure of the nonzero support. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem binary_add_self (v : BinaryVector n) : v + v = 0 := by
  funext j
  exact CharTwo.add_self_eq_zero (v j)

/-- The genuine finite equation system fixing every Boolean coordinate to zero. -/
def originSystem (n : ℕ) : AffineSystem n where
  rows := n
  matrix r j := if j = r then 1 else 0
  rhs _ := 0

@[simp] theorem originSystem_holds (x : Word n) :
    (originSystem n).Holds x ↔ x = origin n := by
  change (∀ r, ∑ j, (if j = r then (1 : ZMod 2) else 0) *
    bitValue (ZMod 2) (x j) = 0) ↔ _
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  constructor
  · intro h
    funext j
    apply bitValue_injective
    exact h j
  · intro h
    subst x
    intro j
    rfl

/-- The translate of a ternary-closed nonempty support is an actual binary
linear subspace. -/
def supportDirections (f : Signature AlgebraicComplex n) (a : Word n)
    (ha : f a ≠ 0)
    (ht : ∀ x y z : Word n, f x ≠ 0 → f y ≠ 0 → f z ≠ 0 →
      f (xor (xor x y) z) ≠ 0) : Submodule (ZMod 2) (BinaryVector n) where
  carrier := {v | f (wordVector (vectorWord a + v)) ≠ 0}
  zero_mem' := by simpa using ha
  add_mem' := by
    intro u v hu hv
    have h := ht (wordVector (vectorWord a + u)) a
      (wordVector (vectorWord a + v)) hu ha hv
    have he : wordVector (vectorWord a + (u + v)) =
        xor (xor (wordVector (vectorWord a + u)) a) (wordVector (vectorWord a + v)) := by
      apply vector_injective
      simp only [vector_word, vector_xor]
      funext j
      simp only [Pi.add_apply]
      have hc : vectorWord a j + vectorWord a j = 0 := CharTwo.add_self_eq_zero _
      linear_combination -hc
    change f (wordVector (vectorWord a + (u + v))) ≠ 0
    rwa [he]
  smul_mem' := by
    intro c v hv
    fin_cases c
    · simpa using ha
    · simpa using hv

/-- Ternary closure alone constructs both finite support equations and an
actual affine retraction onto the nonzero support. -/
theorem exists_support_retraction (f : Signature AlgebraicComplex n)
    (a : Word n) (ha : f a ≠ 0)
    (ht : ∀ x y z : Word n, f x ≠ 0 → f y ≠ 0 → f z ≠ 0 →
      f (xor (xor x y) z) ≠ 0) :
    ∃ (S : AffineSystem n) (p : Word n → Word n), IsAffineMap p ∧
      (∀ x, f (p x) ≠ 0) ∧ (∀ x, f x ≠ 0 → p x = x) ∧
      (∀ x, S.Holds x ↔ f x ≠ 0) := by
  classical
  let D := supportDirections f a ha ht
  obtain ⟨C, hC⟩ := D.exists_isCompl
  let P : BinaryVector n →ₗ[ZMod 2] BinaryVector n := D.projection C hC
  let b := vectorWord a + P (vectorWord a)
  let p := affineBoolean b P
  have hp : IsAffineMap p := affineBoolean_isAffine b P
  have hp_formula (x : Word n) : p x = wordVector (vectorWord a + P (vectorWord a + vectorWord x)) := by
    simp only [p, affineBoolean, b, map_add, add_assoc]
  have hp_nonzero (x : Word n) : f (p x) ≠ 0 := by
    rw [hp_formula]
    exact D.projection_apply_mem hC _
  have hp_fix (x : Word n) (hx : f x ≠ 0) : p x = x := by
    have hxD : vectorWord a + vectorWord x ∈ D := by
      change f (wordVector (vectorWord a + (vectorWord a + vectorWord x))) ≠ 0
      simpa only [← add_assoc, binary_add_self, zero_add, word_vector] using hx
    rw [hp_formula, show P (vectorWord a + vectorWord x) = vectorWord a + vectorWord x from
      D.projection_apply_of_mem_left hC hxD]
    simp only [← add_assoc, binary_add_self, zero_add, word_vector]
  let q := affineBoolean b (LinearMap.id + P)
  have hq : IsAffineMap q := affineBoolean_isAffine b (LinearMap.id + P)
  have hq_formula (x : Word n) : q x = xor (p x) x := by
    apply vector_injective
    simp only [q, p, affineBoolean, vector_word, vector_xor,
      LinearMap.add_apply, LinearMap.id_apply]
    ac_rfl
  let S := (originSystem n).pullback q
  have hS (x : Word n) : S.Holds x ↔ f x ≠ 0 := by
    rw [AffineSystem.pullback_holds _ _ hq, originSystem_holds, hq_formula]
    constructor
    · intro hx
      have hpx : p x = x := by
        have h := congrArg (fun y => xor y x) hx
        simpa only [xor_cancel_right, origin_xor] using h
      simpa only [hpx] using hp_nonzero x
    · intro hx
      rw [hp_fix x hx, AffinePhase.xor_self]
  exact ⟨S, p, hp, hp_nonzero, hp_fix, hS⟩

end
end Holant.ReedMuller.AffinePatching
