import Holant.Proofs.Closure.ClosureSmallArity
import Mathlib.Data.List.FinRange

/-! A finite arity scan of the specified saved decomposition. It selects an
existing slot, preserving duplicate equal-valued factors. No factorization,
class-membership oracle or complexity consumer is used. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArityScan
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open ClosureSmallArity

def firstLarge (n : ℕ) (arity : Fin n → ℕ) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (3 ≤ arity i))

theorem firstLarge_none_iff (n : ℕ) (arity : Fin n → ℕ) :
    firstLarge n arity = none ↔ ∀ i, arity i ≤ 2 := by
  simp [firstLarge, Nat.lt_succ_iff]

theorem firstLarge_sound (n : ℕ) (arity : Fin n → ℕ) (i : Fin n)
    (h : firstLarge n arity = some i) : 3 ≤ arity i := by
  have hh := List.find?_some h
  simpa using hh

noncomputable section
variable {K : Type*} [Field K]

def savedScan {f : AnySignature K} (t : FactorTree f) :
    Option (Fin (packedTree t).decomposition.count) :=
  firstLarge _ (packedTree t).decomposition.arity

theorem savedScan_sound {f : AnySignature K} (t : FactorTree f)
    (i : Fin (packedTree t).decomposition.count) (h : savedScan t = some i) :
    3 ≤ (packedTree t).decomposition.arity i ∧
    (⟨(packedTree t).decomposition.arity i,(packedTree t).decomposition.factor i⟩ : AnySignature K)
      ∈ t.leaves := by
  exact ⟨firstLarge_sound _ _ i h,
    packedTree_leaves t ((Fintype.equivFin (packedTree t).Index).symm i)⟩

theorem savedScan_none_closure {f : AnySignature K} (t : FactorTree f)
    (positive : ∀ g ∈ t.leaves, 0 < g.1) (h : savedScan t = none) :
    Signature.TensorClosure (fun n _ => n = 1 ∨ n = 2) f.2 := by
  refine ⟨(packedTree t).decomposition, ?_, (packedTree t).decomposition_value⟩
  intro i
  have lo := positive _ (packedTree_leaves t ((Fintype.equivFin (packedTree t).Index).symm i))
  have hi := (firstLarge_none_iff _ _).mp h i
  change 0 < (packedTree t).decomposition.arity i at lo
  omega

end
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSmallArityScan
