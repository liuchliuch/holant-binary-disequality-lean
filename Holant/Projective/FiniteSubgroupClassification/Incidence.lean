import Holant.Projective.FiniteSubgroupClassification.FixedPoints
import Holant.Projective.FiniteSubgroupClassification.Stabilizers
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupAction.CardCommute

/-! The finite exceptional-point action and the fixed-point incidence equation
for an arbitrary finite subgroup of the actual complex projective group. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
noncomputable section

/-- Points fixed by a nonidentity element of the given subgroup. -/
noncomputable def exceptionalPoints (H : Subgroup (PGL2 ℂ)) : SubMulAction H ProjectiveLine where
  carrier := {p | ∃ g : H, g ≠ 1 ∧ g • p = p}
  smul_mem' h p hp := by
    obtain ⟨g, hg, hgp⟩ := hp
    refine ⟨h * g * h⁻¹, ?_, ?_⟩
    · intro he
      apply hg
      have := congrArg (fun q : H => h⁻¹ * q * h) he
      simpa [mul_assoc] using this
    · simp [mul_smul, hgp]

theorem exceptionalPoints_finite (H : Subgroup (PGL2 ℂ)) [Finite H] :
    (exceptionalPoints H : Set ProjectiveLine).Finite := by
  let I := {g : H // g ≠ 1}
  have hf : (⋃ g : I, fixedPoints (g.val : PGL2 ℂ)).Finite :=
    Set.finite_iUnion fun g => fixedPoints_finite
      ((Subtype.val_injective.isOfFinOrder_iff (f := H.subtype)).mpr
        (isOfFinOrder_of_finite g.val))
      (fun he => g.property (Subtype.ext he))
  apply hf.subset
  rintro p ⟨g, hg, hp⟩
  exact Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hp⟩

instance (H : Subgroup (PGL2 ℂ)) [Finite H] : Finite (exceptionalPoints H) :=
  (exceptionalPoints_finite H).to_subtype

/-- The orbit set is finite although the entire projective line is infinite. -/
abbrev ExceptionalOrbits (H : Subgroup (PGL2 ℂ)) :=
  Quotient (MulAction.orbitRel H (exceptionalPoints H))

/-- Restricting to exceptional points loses none of a nonidentity element's fixed points. -/
noncomputable def exceptionalFixedEquiv (H : Subgroup (PGL2 ℂ)) (g : H) (hg : g ≠ 1) :
    MulAction.fixedBy (exceptionalPoints H) g ≃ fixedPoints (g : PGL2 ℂ) :=
  Equiv.ofBijective
    (fun p => ⟨p.val.val, congrArg Subtype.val p.property⟩)
    ⟨by
      intro p q h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : fixedPoints (g : PGL2 ℂ) => z.val) h,
      fun p => ⟨⟨⟨p.val, ⟨g, hg, p.property⟩⟩, Subtype.ext p.property⟩, rfl⟩⟩

theorem exceptionalFixed_card (H : Subgroup (PGL2 ℂ)) [Finite H]
    (g : H) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy (exceptionalPoints H) g) = 2 := by
  rw [Nat.card_congr (exceptionalFixedEquiv H g hg)]
  exact fixedPoints_ncard ((Subtype.val_injective.isOfFinOrder_iff (f := H.subtype)).mpr
    (isOfFinOrder_of_finite g))
    (fun he => hg (Subtype.ext he))

/-- The fixed-point incidence equation: each nonidentity group element
contributes exactly two incidences, while identity fixes every exceptional point. -/
theorem exceptional_incidence (H : Subgroup (PGL2 ℂ)) [Finite H] :
    Nat.card (exceptionalPoints H) + 2 * (Nat.card H - 1) =
      Nat.card (ExceptionalOrbits H) * Nat.card H := by
  classical
  letI := Fintype.ofFinite H
  letI := Fintype.ofFinite (exceptionalPoints H)
  letI := Fintype.ofFinite (ExceptionalOrbits H)
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H (exceptionalPoints H)
  have hone : Fintype.card (MulAction.fixedBy (exceptionalPoints H) (1 : H)) =
      Fintype.card (exceptionalPoints H) := by
    exact Fintype.card_congr {
      toFun := Subtype.val
      invFun := fun p => ⟨p, one_smul H p⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum : ∑ g ∈ (Finset.univ : Finset H).erase 1,
      Fintype.card (MulAction.fixedBy (exceptionalPoints H) g) =
      (Fintype.card H - 1) * 2 := by
    calc
      _ = ∑ _g ∈ (Finset.univ : Finset H).erase 1, 2 := by
        apply Finset.sum_congr rfl
        intro g hg
        exact Nat.card_eq_fintype_card.symm.trans
          (exceptionalFixed_card H g (Finset.mem_erase.mp hg).1)
      _ = _ := by simp
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : H)), hone, hsum] at hB
  simpa [Nat.card_eq_fintype_card, add_comm, mul_comm] using hB

/-- The orbit-size form of the same incidence equation. -/
theorem exceptional_orbit_incidence (H : Subgroup (PGL2 ℂ)) [Finite H] :
    letI := Fintype.ofFinite (ExceptionalOrbits H)
    (∑ ω : ExceptionalOrbits H,
      Nat.card H / Nat.card (MulAction.stabilizer H ω.out)) +
      2 * (Nat.card H - 1) = Nat.card (ExceptionalOrbits H) * Nat.card H := by
  classical
  letI := Fintype.ofFinite H
  letI := Fintype.ofFinite (exceptionalPoints H)
  letI := Fintype.ofFinite (ExceptionalOrbits H)
  have hC := MulAction.card_eq_sum_card_group_div_card_stabilizer H (exceptionalPoints H)
  simpa only [Nat.card_eq_fintype_card, hC] using exceptional_incidence H

/-- Restriction to the invariant exceptional set does not change a point stabilizer. -/
theorem exceptional_stabilizer_eq (H : Subgroup (PGL2 ℂ)) (p : exceptionalPoints H) :
    MulAction.stabilizer H p = MulAction.stabilizer H (p : ProjectiveLine) := by
  ext g
  exact Subtype.ext_iff

/-- Every exceptional-point stabilizer is nontrivial, as its definition asserts. -/
theorem exceptional_stabilizer_two_le (H : Subgroup (PGL2 ℂ)) [Finite H]
    (p : exceptionalPoints H) : 2 ≤ Nat.card (MulAction.stabilizer H p) := by
  obtain ⟨g, hg, hgp⟩ := p.property
  have hmem : g ∈ MulAction.stabilizer H p := Subtype.ext hgp
  have hne : (⟨g, hmem⟩ : MulAction.stabilizer H p) ≠ 1 :=
    fun he => hg (congrArg Subtype.val he)
  letI : Nontrivial (MulAction.stabilizer H p) := ⟨⟨⟨g, hmem⟩, 1, hne⟩⟩
  letI := Fintype.ofFinite (MulAction.stabilizer H p)
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- Lagrange's theorem provides the exact divisibility needed by the spherical
signature arithmetic. -/
theorem exceptional_stabilizer_dvd (H : Subgroup (PGL2 ℂ))
    (p : exceptionalPoints H) :
    Nat.card (MulAction.stabilizer H p) ∣ Nat.card H :=
  (MulAction.stabilizer H p).card_subgroup_dvd_card

theorem exceptional_stabilizer_le (H : Subgroup (PGL2 ℂ)) [Finite H]
    (p : exceptionalPoints H) :
    Nat.card (MulAction.stabilizer H p) ≤ Nat.card H :=
  Nat.le_of_dvd Nat.card_pos (exceptional_stabilizer_dvd H p)

end
end Holant.Projective.FiniteSubgroupClassification
