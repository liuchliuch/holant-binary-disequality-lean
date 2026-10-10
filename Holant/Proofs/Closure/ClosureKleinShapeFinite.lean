import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-! NEW_POST_RECOVERY kernel-checked finite-group foundation. Noncyclic order four yields
an actual Klein-four mixin and an actual second element distinct from 1/x. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape

/-- No chosen conjugating basis or row classification occurs here. -/
theorem kleinOfFour (H : Type*) [Group H] (cardinal : Nat.card H = 4)
    (noncyclic : ¬ IsCyclic H) : IsKleinFour H :=
  ⟨cardinal,(not_isCyclic_iff_exponent_eq_prime Nat.prime_two
    (by simpa using cardinal)).mp noncyclic⟩

theorem existsSecond (H : Type*) [Group H] [Fintype H]
    (cardinal : Fintype.card H = 4) (x : H) : ∃ a : H, a ≠ 1 ∧ a ≠ x := by
  classical
  by_contra absent
  have cover : (Finset.univ : Finset H) ⊆ {1,x} := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton]
    by_cases h : a = 1
    · exact .inl h
    · exact .inr (by
        by_contra hx
        exact absent ⟨a,h,hx⟩)
  have lower := Finset.card_le_card cover
  have upper : ({1,x} : Finset H).card ≤ 2 := by
    calc
      _ ≤ ({x} : Finset H).card + 1 := Finset.card_insert_le 1 {x}
      _ = 2 := by simp
  rw [Finset.card_univ,cardinal] at lower
  omega

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureKleinShape
end
