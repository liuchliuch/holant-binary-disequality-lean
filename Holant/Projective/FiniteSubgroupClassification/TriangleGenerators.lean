import Holant.Projective.FiniteGroupFacts.PlatonicStructure
import Holant.Projective.FiniteSubgroupClassification.Action

/-! Explicit `(2,3,5)` generators of the actual alternating group on five
letters, and their transport to projective subgroups. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
noncomputable section

def a5TriangleA : A5 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
def a5TriangleB : A5 := ⟨Equiv.swap 0 2 * Equiv.swap 2 4, by simp [Equiv.Perm.mem_alternatingGroup]⟩

theorem a5TriangleA_order : orderOf a5TriangleA = 2 :=
  orderOf_eq_prime (by decide +kernel : a5TriangleA ^ 2 = 1) (by decide +kernel)

theorem a5TriangleB_order : orderOf a5TriangleB = 3 :=
  orderOf_eq_prime (by decide +kernel : a5TriangleB ^ 3 = 1) (by decide +kernel)

theorem a5TriangleAB_order : orderOf (a5TriangleA * a5TriangleB) = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel : (a5TriangleA * a5TriangleB) ^ 5 = 1) (by decide +kernel)

/-- The explicit pair generates all of A5: its subgroup order is divisible
by 2,3,5, and A5 has no index-two subgroup. -/
theorem a5Triangle_generates :
    Subgroup.closure ({a5TriangleA, a5TriangleB} : Set A5) = ⊤ := by
  let L := Subgroup.closure ({a5TriangleA, a5TriangleB} : Set A5)
  have ha : a5TriangleA ∈ L := Subgroup.subset_closure (by simp)
  have hb : a5TriangleB ∈ L := Subgroup.subset_closure (by simp)
  have h2 : 2 ∣ Nat.card L := by
    simpa [a5TriangleA_order] using orderOf_dvd_natCard (⟨a5TriangleA, ha⟩ : L)
  have h3 : 3 ∣ Nat.card L := by
    simpa [a5TriangleB_order] using orderOf_dvd_natCard (⟨a5TriangleB, hb⟩ : L)
  have h5 : 5 ∣ Nat.card L := by
    simpa [a5TriangleAB_order] using orderOf_dvd_natCard (⟨a5TriangleA * a5TriangleB, L.mul_mem ha hb⟩ : L)
  have h30 : 30 ∣ Nat.card L :=
    (show Nat.Coprime 6 5 by decide).mul_dvd_of_dvd_of_dvd
      ((show Nat.Coprime 2 3 by decide).mul_dvd_of_dvd_of_dvd h2 h3) h5
  have hA5 : Nat.card A5 = 60 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  have hle : Nat.card L ≤ 60 := Nat.le_of_dvd (by decide) (hA5 ▸ L.card_subgroup_dvd_card)
  have hp : 0 < Nat.card L := Nat.card_pos
  have hcard : Nat.card L = 30 ∨ Nat.card L = 60 := by
    obtain ⟨k, hk⟩ := h30
    omega
  rcases hcard with h30 | h60
  · have hi : L.index = 2 := by
      have h := L.index_mul_card
      rw [h30, hA5] at h
      omega
    exact (a5_no_index_two L hi).elim
  · exact Subgroup.eq_top_of_card_eq L (h60.trans hA5.symm)

/-- Transporting the actual generating pair through a group isomorphism. -/
theorem exists_triangle_generators {G : Type*} [Group G] (e : G ≃* A5) :
    ∃ a b : G, orderOf a = 2 ∧ orderOf b = 3 ∧ orderOf (a * b) = 5 ∧
      Subgroup.closure ({a, b} : Set G) = ⊤ := by
  refine ⟨e.symm a5TriangleA, e.symm a5TriangleB,
    (e.symm.orderOf_eq _).trans a5TriangleA_order,
    (e.symm.orderOf_eq _).trans a5TriangleB_order, ?_, ?_⟩
  · rw [← map_mul, MulEquiv.orderOf_eq]
    exact a5TriangleAB_order
  · have h := congrArg (fun L : Subgroup A5 => L.map e.symm.toMonoidHom) a5Triangle_generates
    have hr : e.symm.toMonoidHom.range = ⊤ := e.symm.toMonoidHom.range_eq_top.mpr e.symm.surjective
    simp only [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, hr] at h
    exact h

/-- An abstract A5 identification supplies a genuine matrix-generating pair. -/
theorem exists_projective_triangle_generators (H : Subgroup (PGL2 ℂ)) (e : H ≃* A5) :
    ∃ a b : PGL2 ℂ, a ∈ H ∧ b ∈ H ∧ orderOf a = 2 ∧ orderOf b = 3 ∧
      orderOf (a * b) = 5 ∧ Subgroup.closure ({a, b} : Set (PGL2 ℂ)) = H := by
  obtain ⟨a, b, ha, hb, hab, hgen⟩ := exists_triangle_generators e
  refine ⟨a, b, a.property, b.property, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.orderOf_coe a).trans ha
  · exact (Subgroup.orderOf_coe b).trans hb
  · exact (Subgroup.orderOf_coe (a * b)).trans hab
  · have h := congrArg (fun L : Subgroup H => L.map H.subtype) hgen
    simp only [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, H.range_subtype] at h
    exact h

end
end Holant.Projective.FiniteSubgroupClassification
