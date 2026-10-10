import Holant.Projective.FiniteSubgroupClassification.Incidence
import Holant.Projective.FiniteSubgroupClassification.SphericalArithmetic

/-! Spherical signatures of actual finite subgroups of `PGL2 ℂ`, obtained from
the actual projective-line action. These are geometric restrictions; identifying
the noncyclic signatures with displayed matrix models is a separate theorem. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
noncomputable section

/-- Stabilizer order at a representative of an exceptional orbit. -/
def stabilizerOrder (H : Subgroup (PGL2 ℂ)) (ω : ExceptionalOrbits H) : ℕ :=
  Nat.card (MulAction.stabilizer H ω.out)

/-- Reciprocal form of the incidence equation for the actual finite action. -/
theorem exceptional_rational_incidence (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : 1 < Nat.card H) :
    letI := Fintype.ofFinite (ExceptionalOrbits H)
    ∑ ω : ExceptionalOrbits H, (1 - 1 / (stabilizerOrder H ω : ℚ)) =
      2 - 2 / (Nat.card H : ℚ) := by
  letI := Fintype.ofFinite (ExceptionalOrbits H)
  apply spherical_incidence_of_nat (Nat.card H) (stabilizerOrder H) hH
  · exact fun ω => exceptional_stabilizer_dvd H ω.out
  · simpa only [Nat.card_eq_fintype_card, stabilizerOrder] using exceptional_orbit_incidence H

/-- A nontrivial finite projective subgroup has exactly two or three
exceptional orbits. -/
theorem exceptional_orbits_card (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : 1 < Nat.card H) :
    Nat.card (ExceptionalOrbits H) = 2 ∨ Nat.card (ExceptionalOrbits H) = 3 := by
  letI := Fintype.ofFinite (ExceptionalOrbits H)
  simpa only [Nat.card_eq_fintype_card] using
    spherical_orbit_card (Nat.card H) (stabilizerOrder H) hH
      (fun ω => exceptional_stabilizer_two_le H ω.out)
      (fun ω => exceptional_stabilizer_le H ω.out)
      (exceptional_rational_incidence H hH)

/-- Both stabilizers in the two-orbit case are the full group. -/
theorem exceptional_two_stabilizers (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : 1 < Nat.card H) (hcard : Nat.card (ExceptionalOrbits H) = 2) :
    ∀ ω, stabilizerOrder H ω = Nat.card H := by
  letI := Fintype.ofFinite (ExceptionalOrbits H)
  exact spherical_two_orbits (Nat.card H) (stabilizerOrder H) hH
    (fun ω => exceptional_stabilizer_two_le H ω.out)
    (fun ω => exceptional_stabilizer_le H ω.out)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
    (exceptional_rational_incidence H hH)

/-- The geometric two-orbit case is genuinely cyclic. -/
theorem exceptional_two_orbits_isCyclic (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : 1 < Nat.card H) (hcard : Nat.card (ExceptionalOrbits H) = 2) :
    IsCyclic H := by
  have hnonempty : Nonempty (ExceptionalOrbits H) :=
    (Nat.card_pos_iff.mp (by omega : 0 < Nat.card (ExceptionalOrbits H))).1
  obtain ⟨ω⟩ := hnonempty
  have he : MulAction.stabilizer H ω.out = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (MulAction.stabilizer H ω.out)).mp (exceptional_two_stabilizers H hH hcard ω)
  apply finite_subgroup_fixing_point_isCyclic H (ω.out : ProjectiveLine)
  intro q hq
  have hmem : (⟨q, hq⟩ : H) ∈ MulAction.stabilizer H ω.out := by rw [he]; trivial
  exact congrArg Subtype.val hmem

/-- Any three natural numbers can be sorted by a permutation of their indices. -/
theorem exists_sorted_perm_three (f : Fin 3 → ℕ) :
    ∃ e : Equiv.Perm (Fin 3), f (e 0) ≤ f (e 1) ∧ f (e 1) ≤ f (e 2) := by
  classical
  by_cases h01 : f 0 ≤ f 1
  · by_cases h12 : f 1 ≤ f 2
    · exact ⟨1, h01, h12⟩
    · by_cases h02 : f 0 ≤ f 2
      · refine ⟨Equiv.swap 1 2, ?_⟩
        simp only [Equiv.swap_apply_def]
        norm_num
        omega
      · refine ⟨Equiv.swap 0 1 * Equiv.swap 0 2, ?_⟩
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        norm_num
        omega
  · by_cases h02 : f 0 ≤ f 2
    · refine ⟨Equiv.swap 0 1, ?_⟩
      simp only [Equiv.swap_apply_def]
      norm_num
      omega
    · by_cases h12 : f 1 ≤ f 2
      · refine ⟨Equiv.swap 0 2 * Equiv.swap 0 1, ?_⟩
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
        norm_num
        omega
      · refine ⟨Equiv.swap 0 2, ?_⟩
        simp only [Equiv.swap_apply_def]
        norm_num
        omega

/-- The full spherical signature restriction for three actual exceptional orbits. -/
theorem exceptional_three_signature (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : 1 < Nat.card H) (hcard : Nat.card (ExceptionalOrbits H) = 3) :
    ∃ e : Fin 3 ≃ ExceptionalOrbits H,
      let a := stabilizerOrder H (e 0)
      let b := stabilizerOrder H (e 1)
      let c := stabilizerOrder H (e 2)
      (a = 2 ∧ b = 2 ∧ Nat.card H = 2 * c) ∨
      (a = 2 ∧ b = 3 ∧ c = 3 ∧ Nat.card H = 12) ∨
      (a = 2 ∧ b = 3 ∧ c = 4 ∧ Nat.card H = 24) ∨
      (a = 2 ∧ b = 3 ∧ c = 5 ∧ Nat.card H = 60) := by
  classical
  letI := Fintype.ofFinite (ExceptionalOrbits H)
  let e₀ : Fin 3 ≃ ExceptionalOrbits H :=
    (Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  obtain ⟨σ, hs⟩ := exists_sorted_perm_three (fun i => stabilizerOrder H (e₀ i))
  let e := σ.trans e₀
  have hs0 : stabilizerOrder H (e 0) ≤ stabilizerOrder H (e 1) := hs.1
  have hs1 : stabilizerOrder H (e 1) ≤ stabilizerOrder H (e 2) := hs.2
  have hi := exceptional_rational_incidence H hH
  have heq : (∑ i : Fin 3, (1 - 1 / (stabilizerOrder H (e i) : ℚ))) =
      ∑ ω : ExceptionalOrbits H, (1 - 1 / (stabilizerOrder H ω : ℚ)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [← heq, Fin.sum_univ_three] at hi
  exact ⟨e, spherical_three_orders (Nat.card H) _ _ _ hH
    (exceptional_stabilizer_two_le H (e 0).out) hs0 hs1 hi⟩

end
end Holant.Projective.FiniteSubgroupClassification
