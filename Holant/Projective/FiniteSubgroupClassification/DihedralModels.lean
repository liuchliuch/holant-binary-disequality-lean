import Holant.Projective.FiniteSubgroupClassification.CyclicConjugacy
import Holant.Projective.FiniteSubgroupClassification.KleinConjugacy

/-! The source's actual standard dihedral matrix subgroups, their rotation and
reflection carriers, and their cardinalities. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

theorem torus_mul_xClass {q : PGL2 ℂ} (hq : q ∈ diagonalTorus) :
    q * xClass = xClass * q⁻¹ := by
  obtain ⟨a, rfl⟩ := hq
  rw [← map_inv]
  simpa only [inv_inv] using (xClass_mul_torus a⁻¹).symm

theorem xClass_not_mem_torus : xClass ∉ diagonalTorus := by
  intro hx
  have hdiag : xClass ∈ diagonalClasses := by rwa [← diagonalTorus_carrier]
  exact Set.disjoint_left.mp diagonal_antidiagonal_disjoint hdiag ⟨1, 1, rfl⟩

/-- Adjoining coordinate interchange to a subgroup of the diagonal torus. -/
noncomputable def reflectedTorus (K : Subgroup (PGL2 ℂ)) (hK : K ≤ diagonalTorus) : Subgroup (PGL2 ℂ) where
  carrier := {q | q ∈ K ∨ ∃ r ∈ K, q = xClass * r}
  one_mem' := Or.inl K.one_mem
  mul_mem' := by
    rintro p q (hp | ⟨r, hr, rfl⟩) (hq | ⟨s, hs, rfl⟩)
    · exact Or.inl (K.mul_mem hp hq)
    · right
      refine ⟨p⁻¹ * s, K.mul_mem (K.inv_mem hp) hs, ?_⟩
      rw [← mul_assoc, torus_mul_xClass (hK hp), mul_assoc]
    · exact Or.inr ⟨r * q, K.mul_mem hr hq, mul_assoc _ _ _⟩
    · left
      have hxx : xClass * xClass = 1 := by simpa only [pow_two] using xClass_square
      have he : (xClass * r) * (xClass * s) = r⁻¹ * s := by
        calc
          _ = xClass * (r * xClass) * s := by group
          _ = r⁻¹ * s := by rw [torus_mul_xClass (hK hr), ← mul_assoc, hxx, one_mul]
      rw [he]
      exact K.mul_mem (K.inv_mem hr) hs
  inv_mem' := by
    rintro p (hp | ⟨r, hr, rfl⟩)
    · exact Or.inl (K.inv_mem hp)
    · right
      refine ⟨r, hr, ?_⟩
      have hxx : xClass⁻¹ = xClass := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using xClass_square)
      rw [mul_inv_rev, hxx, torus_mul_xClass (hK (K.inv_mem hr)), inv_inv]

@[simp] theorem mem_reflectedTorus {K : Subgroup (PGL2 ℂ)} {hK : K ≤ diagonalTorus}
    (q : PGL2 ℂ) : q ∈ reflectedTorus K hK ↔ q ∈ K ∨ ∃ r ∈ K, q = xClass * r := Iff.rfl

/-- The two cosets are disjoint because coordinate interchange is antidiagonal. -/
theorem reflection_not_mem_torus {r : PGL2 ℂ} (hr : r ∈ diagonalTorus) :
    xClass * r ∉ diagonalTorus := by
  intro h
  apply xClass_not_mem_torus
  simpa [mul_assoc] using diagonalTorus.mul_mem h (diagonalTorus.inv_mem hr)

/-- The actual rotation/reflection partition gives a two-copy equivalence. -/
noncomputable def reflectedTorusEquiv (K : Subgroup (PGL2 ℂ)) (hK : K ≤ diagonalTorus) :
    Bool × K ≃ reflectedTorus K hK :=
  Equiv.ofBijective (fun p => if p.1 then
    ⟨xClass * p.2, Or.inr ⟨p.2, p.2.property, rfl⟩⟩ else ⟨p.2, Or.inl p.2.property⟩)
    ⟨by
      rintro ⟨b, r⟩ ⟨c, s⟩ h
      cases b <;> cases c <;> dsimp at h
      · have he : (r : PGL2 ℂ) = s :=
          congrArg (fun z : reflectedTorus K hK => (z : PGL2 ℂ)) h
        exact Prod.ext rfl (Subtype.ext he)
      · have he : (r : PGL2 ℂ) = xClass * s :=
          congrArg (fun z : reflectedTorus K hK => (z : PGL2 ℂ)) h
        exact (reflection_not_mem_torus (hK s.property) (he ▸ hK r.property)).elim
      · have he : xClass * r = (s : PGL2 ℂ) :=
          congrArg (fun z : reflectedTorus K hK => (z : PGL2 ℂ)) h
        exact (reflection_not_mem_torus (hK r.property) (he.symm ▸ hK s.property)).elim
      · have he : xClass * r = xClass * s :=
          congrArg (fun z : reflectedTorus K hK => (z : PGL2 ℂ)) h
        exact Prod.ext rfl (Subtype.ext (mul_left_cancel he)), by
      rintro ⟨q, hq | ⟨r, hr, rfl⟩⟩
      · exact ⟨⟨false, ⟨q, hq⟩⟩, rfl⟩
      · exact ⟨⟨true, ⟨r, hr⟩⟩, rfl⟩⟩

theorem reflectedTorus_card (K : Subgroup (PGL2 ℂ)) (hK : K ≤ diagonalTorus) :
    Nat.card (reflectedTorus K hK) = 2 * Nat.card K := by
  rw [← Nat.card_congr (reflectedTorusEquiv K hK), Nat.card_prod]
  simp

theorem cyclicModel_le_torus (ω : ℂˣ) : cyclicModel ω ≤ diagonalTorus := by
  apply Subgroup.zpowers_le.mpr
  rw [cyclicGenerator_eq_torus]
  exact ⟨ω⁻¹, rfl⟩

/-- The actual standard dihedral subgroup from the source's matrix display. -/
noncomputable def dihedralModel (ω : ℂˣ) : Subgroup (PGL2 ℂ) :=
  reflectedTorus (cyclicModel ω) (cyclicModel_le_torus ω)

/-- Its carrier is exactly the displayed rotations and antidiagonal reflection coset. -/
theorem mem_dihedralModel_iff {ω : ℂˣ} {m : ℕ} (hm : 0 < m)
    (hω : IsPrimitiveRoot ω m) (q : PGL2 ℂ) :
    q ∈ dihedralModel ω ↔
      (∃ k < m, q = pglMk ℂ (diagonalGL 1 (ω ^ k))) ∨
      ∃ k < m, q = pglMk ℂ (xGL * diagonalGL 1 (ω ^ k)) := by
  change (q ∈ cyclicModel ω ∨ ∃ r ∈ cyclicModel ω, q = xClass * r) ↔ _
  rw [mem_cyclicModel_iff hm hω]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (mem_cyclicModel_iff hm hω r).mp hr
    exact ⟨k, hk, (map_mul (pglMk ℂ) _ _).symm⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨pglMk ℂ (diagonalGL 1 (ω ^ k)), (mem_cyclicModel_iff hm hω _).mpr ⟨k, hk, rfl⟩, ?_⟩
    exact map_mul (pglMk ℂ) _ _

theorem dihedralModel_card {ω : ℂˣ} {m : ℕ} (hω : IsPrimitiveRoot ω m) :
    Nat.card (dihedralModel ω) = 2 * m := by
  rw [dihedralModel, reflectedTorus_card, cyclicModel_card, ← hω.eq_orderOf]

/-- A finite diagonal subgroup is itself a displayed cyclic model. -/
theorem finite_torus_subgroup_eq_cyclicModel (K : Subgroup (PGL2 ℂ)) [Finite K]
    (hK : K ≤ diagonalTorus) :
    ∃ ω : ℂˣ, IsPrimitiveRoot ω (Nat.card K) ∧ K = cyclicModel ω := by
  letI : IsCyclic K := finite_diagonal_subgroup_isCyclic K hK
  obtain ⟨q, hq⟩ := K.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hqmem : q ∈ K := hq ▸ Subgroup.mem_zpowers q
  obtain ⟨a, ha⟩ := hK hqmem
  refine ⟨a⁻¹, ?_, ?_⟩
  · apply IsPrimitiveRoot.iff_orderOf.mpr
    rw [orderOf_inv, ← orderOf_injective torusHom torusHom_injective, ha, ← hq, Nat.card_zpowers]
  · rw [← hq, cyclicModel, cyclicGenerator_eq_torus, inv_inv, ha]

end
end Holant.Projective.FiniteSubgroupClassification
