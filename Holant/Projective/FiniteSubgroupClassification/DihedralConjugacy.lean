import Holant.Projective.FiniteSubgroupClassification.DihedralModels
import Holant.Projective.FiniteSubgroupClassification.NormalKlein

/-! Actual dihedral conjugacy for finite noncyclic subgroups preserving the two
coordinate lines setwise, expressed here by the checked centralizer of `[Z]`. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

theorem torus_commute_z (a : ℂˣ) : Commute (torusHom a) zClass := by
  rw [← torus_neg_one]
  exact (Commute.all a (-1)).map torusHom

/-- A subgroup of the diagonal/antidiagonal group containing coordinate
interchange is exactly its rotations together with the reflection coset. -/
theorem subgroup_centralizer_eq_reflectedTorus
    (H : Subgroup (PGL2 ℂ))
    (hH : H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)))
    (hx : xClass ∈ H) :
    H = reflectedTorus (H ⊓ diagonalTorus) inf_le_right := by
  apply le_antisymm
  · intro q hq
    have hmem : q ∈ diagonalClasses ∪ antidiagonalClasses := by
      rw [← centralizer_z]
      exact hH hq
    rcases hmem with hd | ha
    · exact Or.inl ⟨hq, by
        change q ∈ (diagonalTorus : Set (PGL2 ℂ))
        rwa [diagonalTorus_carrier]⟩
    · obtain ⟨a, b, hq'⟩ := ha
      right
      refine ⟨xClass * q, ⟨H.mul_mem hx hq, ?_⟩, ?_⟩
      · rw [hq', antidiagonal_factor, ← mul_assoc, xClass_mul_torus, mul_assoc]
        have hxx : xClass * xClass = 1 := by simpa only [pow_two] using xClass_square
        rw [hxx, mul_one]
        exact ⟨(a * b⁻¹)⁻¹, rfl⟩
      · have hxx : xClass * xClass = 1 := by simpa only [pow_two] using xClass_square
        rw [← mul_assoc, hxx, one_mul]
  · rintro q (hq | ⟨r, hr, rfl⟩)
    · exact hq.1
    · exact H.mul_mem hx hr.1

/-- Every finite noncyclic subgroup of the actual diagonal/antidiagonal group
is conjugate to a displayed standard dihedral matrix model with parameter ≥2. -/
theorem finite_centralizer_noncyclic_conjugacy
    (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : H ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)))
    (hnc : ¬IsCyclic H) :
    ∃ t : ℂˣ, ∃ ω : ℂˣ, ∃ m : ℕ, 2 ≤ m ∧ IsPrimitiveRoot ω m ∧
      H.map (MulAut.conj (torusHom t)).toMonoidHom = dihedralModel ω ∧
      Nat.card H = 2 * m := by
  have hnot : ¬H ≤ diagonalTorus := fun h => hnc (finite_diagonal_subgroup_isCyclic H h)
  obtain ⟨q, hq, hqT⟩ := Set.not_subset.mp hnot
  have hanti : q ∈ antidiagonalClasses := by
    have hmem : q ∈ diagonalClasses ∪ antidiagonalClasses := by
      rw [← centralizer_z]
      exact hH hq
    rcases hmem with hd | ha
    · exact (hqT (by rwa [diagonalTorus_carrier])).elim
    · exact ha
  obtain ⟨t, ht⟩ := exists_torus_conjugate_antidiagonal hanti
  let e := MulAut.conj (torusHom t)
  let H' := H.map e.toMonoidHom
  letI : Finite H' := Finite.of_equiv H
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toEquiv
  have hH' : H' ≤ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
    rintro r ⟨s, hs, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hc : Commute s zClass := Subgroup.mem_centralizer_singleton_iff.mp (hH hs)
    have he : e zClass = zClass := by
      change torusHom t * zClass * (torusHom t)⁻¹ = zClass
      rw [(torus_commute_z t).eq]
      simp [mul_assoc]
    exact he ▸ (hc.map e.toMonoidHom).eq
  have hx : xClass ∈ H' := ⟨q, hq, ht⟩
  let K := H' ⊓ diagonalTorus
  letI : Finite K := Finite.of_injective (Subgroup.inclusion (show K ≤ H' from inf_le_left))
    (Subgroup.inclusion_injective _)
  obtain ⟨ω, hω, hK⟩ := finite_torus_subgroup_eq_cyclicModel K inf_le_right
  have he : H' = dihedralModel ω := by
    rw [subgroup_centralizer_eq_reflectedTorus H' hH' hx]
    change reflectedTorus K _ = reflectedTorus (cyclicModel ω) _
    subst K
    congr
  have hc : Nat.card H = 2 * Nat.card K := by
    rw [← card_conjugate_subgroup H (torusHom t)]
    change Nat.card H' = _
    rw [subgroup_centralizer_eq_reflectedTorus H' hH' hx, reflectedTorus_card]
  have hm : 2 ≤ Nat.card K := by
    have hp : 0 < Nat.card K := Nat.card_pos
    by_contra hn
    have hk1 : Nat.card K = 1 := by omega
    have hH2 : Nat.card H = 2 := by simpa [hk1] using hc
    exact hnc (isCyclic_of_prime_card (p := 2) hH2)
  exact ⟨t, ω, Nat.card K, hm, hω, he, hc⟩

end
end Holant.Projective.FiniteSubgroupClassification
