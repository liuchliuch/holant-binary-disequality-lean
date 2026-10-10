import Holant.ReedMuller.LowArity.Matching
import Holant.TensorClosure
import Mathlib.Analysis.Complex.Basic

namespace Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section

def bit (b : Bool) : ZMod 2 := if b then 1 else 0

def flatSignature {n : ℕ} (c : ℂˣ) (a : BinaryVector n) (D : BinaryCode n) : Signature ℂ n :=
  by
    classical
    exact fun x => if (fun i => bit (x i)-a i) ∈ D then (c:ℂ) else 0

def shiftedBinary (a b : ZMod 2) : Signature ℂ 2 :=
  fun x => if bit (x 0)-a = bit (x 1)-b then 1 else 0

private theorem shifted_bit_test : ∀ a b : ZMod 2, ∀ x y : Bool,
    (bit x-a=bit y-b) ↔ (if a=b then x=y else x≠y) := by decide

/-- Every factor is literally I or X, not an arbitrary weighted binary. -/
theorem shiftedBinary_eq (a b : ZMod 2) :
    shiftedBinary a b = if a=b then (fun x : Fin 2 → Bool => Signature.equality (x 0) (x 1)) else (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  funext x
  simp only [shiftedBinary,shifted_bit_test]
  by_cases hab : a=b
  · simp [hab,Signature.equality]
  · simp [hab,Signature.disequality]

def flatDecomposition {r n : ℕ} (M : Matching r n) (c : ℂˣ) (a : BinaryVector n) :
    TensorDecomposition ℂ n where
  count := r
  arity := fun _ => 2
  factor := fun e => shiftedBinary (a (M (e,0))) (a (M (e,1)))
  ports := (Equiv.sigmaEquivProd (Fin r) (Fin 2)).trans M
  scale := c

theorem flatDecomposition_value {r n : ℕ} (M : Matching r n) (c : ℂˣ)
    (a : BinaryVector n) (D : BinaryCode n) (hD : ∀ x, x ∈ D ↔ M.Holds x) :
    (flatDecomposition M c a).value = flatSignature c a D := by
  funext x
  change (c:ℂ) * (∏ e, if bit (x (M (e,0)))-a (M (e,0)) =
      bit (x (M (e,1)))-a (M (e,1)) then (1:ℂ) else 0) = _
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one]
  simp only [flatSignature,hD,Matching.Holds]
  split_ifs <;> simp_all

/-- Full signature consequence of source Lemma7.16, with every original port,
shift bit, projective scalar and binary factor recorded. -/
theorem low_arity_flat_matching (r : ℕ) (hr : r ≤ 3)
    (D : BinaryCode (2*r)) (hD : SelfDual D) (c : ℂˣ) (a : BinaryVector (2*r)) :
    ∃ M : Matching r (2*r),
      (∀ x, x ∈ D ↔ M.Holds x) ∧
      (flatDecomposition M c a).value = flatSignature c a D ∧
      ∀ e, (flatDecomposition M c a).factor e = (fun x : Fin 2 → Bool => Signature.equality (x 0) (x 1)) ∨
        (flatDecomposition M c a).factor e = (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  obtain ⟨M,hM⟩ := low_arity_matching r hr D hD
  refine ⟨M,hM,flatDecomposition_value M c a D hM,?_⟩
  intro e
  change shiftedBinary _ _ = _ ∨ shiftedBinary _ _ = _
  rw [shiftedBinary_eq]
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end
end Holant.ReedMuller.LowArity
