import Holant.Projective.FiniteSubgroupClassification.PairOrbit
import Holant.Projective.FiniteSubgroupClassification.DihedralIsomorphism
import Holant.Projective.FiniteSubgroupClassification.TetrahedralCase
import Holant.Projective.FiniteSubgroupClassification.OctahedralStructure
import Holant.Projective.FiniteSubgroupClassification.ElementOrders

/-! Genuine finite-projective-group classification through the cyclic,
dihedral, tetrahedral and octahedral branches. The only alternative retained
by this reduction is the actual order-sixty `(2,3,5)` geometric signature. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
noncomputable section

/-- Conjugacy to one of the first four displayed source models. -/
def ClassifiedWithoutIcosahedral (H : Subgroup (PGL2 ℂ)) : Prop :=
  (∃ g : PGL2 ℂ, ∃ ω : ℂˣ, ∃ m : ℕ, 0 < m ∧ IsPrimitiveRoot ω m ∧
    H.map (MulAut.conj g).toMonoidHom = cyclicModel ω) ∨
  (∃ g : PGL2 ℂ, ∃ ω : ℂˣ, ∃ m : ℕ, 2 ≤ m ∧ IsPrimitiveRoot ω m ∧
    H.map (MulAut.conj g).toMonoidHom = dihedralModel ω) ∨
  (∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .tetrahedral) ∨
  (∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .octahedral)

/-- The actual `(2,3,4)` branch has the displayed octahedral conjugacy conclusion. -/
theorem exceptional_234_conjugacy (H : Subgroup (PGL2 ℂ)) [Finite H]
    (e : Fin 3 ≃ ExceptionalOrbits H)
    (h0 : stabilizerOrder H (e 0) = 2)
    (h1 : stabilizerOrder H (e 1) = 3)
    (h2 : stabilizerOrder H (e 2) = 4) (hcard : Nat.card H = 24) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom = modelPGL .octahedral :=
  card_twentyfour_no_order_six_conjugacy H hcard (exceptional_234_no_order_six H e h0 h1 h2)

/-- Every finite actual projective subgroup is conjugate to C, D, T or O,
or has exactly the order-sixty `(2,3,5)` signature. -/
theorem finite_subgroup_reduction (H : Subgroup (PGL2 ℂ)) [Finite H] :
    ClassifiedWithoutIcosahedral H ∨
      (Nat.card H = 60 ∧ ∃ e : Fin 3 ≃ ExceptionalOrbits H,
        stabilizerOrder H (e 0) = 2 ∧ stabilizerOrder H (e 1) = 3 ∧
        stabilizerOrder H (e 2) = 5) := by
  classical
  by_cases hcyc : IsCyclic H
  · letI : IsCyclic H := hcyc
    obtain ⟨g, ω, hω, he⟩ := finite_cyclic_subgroup_conjugacy H
    exact Or.inl (Or.inl ⟨g, ω, Nat.card H, Nat.card_pos, hω, he⟩)
  · have hnontrivial : Nontrivial H := Nontrivial.of_not_isCyclic hcyc
    letI : Nontrivial H := hnontrivial
    letI := Fintype.ofFinite H
    have hH : 1 < Nat.card H := by simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card (α := H))
    rcases exceptional_orbits_card H hH with htwo | hthree
    · exact (hcyc (exceptional_two_orbits_isCyclic H hH htwo)).elim
    · obtain ⟨e, he⟩ := exceptional_three_signature H hH hthree
      rcases he with hd | ht | ho | hi
      · obtain ⟨g, ω, hω, he⟩ := exceptional_22m_conjugacy H hcyc e hd.1 hd.2.1 hd.2.2
        exact Or.inl (Or.inr (Or.inl ⟨g, ω, stabilizerOrder H (e 2),
          exceptional_stabilizer_two_le H (e 2).out, hω, he⟩))
      · exact Or.inl (Or.inr (Or.inr (Or.inl
          (exceptional_233_conjugacy H e ht.1 ht.2.1 ht.2.2.1 ht.2.2.2))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr
          (exceptional_234_conjugacy H e ho.1 ho.2.1 ho.2.2.1 ho.2.2.2))))
      · exact Or.inr ⟨hi.2.2.2, e, hi.1, hi.2.1, hi.2.2.1⟩

/-- Complete actual model conjugacy away from group order sixty. -/
theorem finite_subgroup_classification_of_card_ne_sixty
    (H : Subgroup (PGL2 ℂ)) [Finite H] (h60 : Nat.card H ≠ 60) :
    ClassifiedWithoutIcosahedral H := by
  rcases finite_subgroup_reduction H with h | h
  · exact h
  · exact (h60 h.1).elim

end
end Holant.Projective.FiniteSubgroupClassification
