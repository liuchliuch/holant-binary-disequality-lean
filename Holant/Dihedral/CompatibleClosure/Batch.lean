import Holant.Dihedral.CompatibleClosure.GlobalTrace

/-! All common untagged factors can be closed: finite independent actual phase
choices have a nonzero total trace multiplier and preserve a protected minor. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

variable {J : Type*} [Fintype J]

/-- The source's plural common-factor closure has one phase choice per original
factor, derived simultaneously from the actual finite phase grid. -/
theorem finite_untagged_traces {m : ℕ} (hm : 3 ≤ m) (A B : J → Mat)
    (hA : ∀ j, A j ∈ groupM m) (hB : ∀ j, ProjectivelyEqual (B j) (A j)) :
    ∃ γ : J → Bool, ∃ t : J → Scalar, (∀ j, Roots m (t j)) ∧
      (∀ j, trace (A j) (M (γ j) (t j)) ≠ 0) ∧
      (∀ j, trace (B j) (M (γ j) (t j)) ≠ 0) ∧
      (∏ j, trace (A j) (M (γ j) (t j))) ≠ 0 ∧
      (∏ j, trace (B j) (M (γ j) (t j))) ≠ 0 := by
  choose γ t ht h₀ h₁ using fun j => untagged_trace_phase hm (A j) (B j) (hA j) (hB j)
  exact ⟨γ,t,ht,h₀,h₁,Finset.prod_ne_zero_iff.mpr (fun j _ => h₀ j),
    Finset.prod_ne_zero_iff.mpr (fun j _ => h₁ j)⟩

/-- The independent trace factors are the literal complete Boolean assignment
sum, not a product of values declared to be free operations. -/
theorem all_trace_sum [DecidableEq J] (A C : J → Mat) :
    (∑ z : J → Bool × Bool, ∏ j, A j (z j).1 (z j).2 * C j (z j).1 (z j).2) =
      ∏ j, trace (A j) (C j) := by
  have ht (j : J) : trace (A j) (C j) =
      ∑ ab : Bool × Bool, A j ab.1 ab.2 * C j ab.1 ab.2 := by
    rw [Fintype.sum_prod_type]
    rfl
  simp only [ht]
  rw [Fintype.prod_sum]

/-- The protected coefficient determinant accumulates exactly the two full
nonzero trace products, so any finite common closure preserves the tag. -/
theorem batch_protected (γ : J → Bool) (t : J → Scalar) (A B : J → Mat)
    (h₀ : ∀ j, trace (A j) (M (γ j) (t j)) ≠ 0)
    (h₁ : ∀ j, trace (B j) (M (γ j) (t j)) ≠ 0)
    (u₀ v₀ u₁ v₁ : Scalar) (h : u₀*v₁-v₀*u₁ ≠ 0) :
    let c₀ := ∏ j, trace (A j) (M (γ j) (t j))
    let c₁ := ∏ j, trace (B j) (M (γ j) (t j))
    (c₀*u₀)*(c₁*v₁)-(c₀*v₀)*(c₁*u₁) = (c₀*c₁)*(u₀*v₁-v₀*u₁) ∧
      (c₀*u₀)*(c₁*v₁)-(c₀*v₀)*(c₁*u₁) ≠ 0 := by
  constructor
  · exact protected_determinant _ _ _ _ _ _
  · exact protected_determinant_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => h₀ j))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => h₁ j)) h

end Holant.Dihedral.CompatibleClosure
