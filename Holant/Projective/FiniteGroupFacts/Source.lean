import Holant.Projective.FiniteGroupFacts.CyclicDihedral
import Holant.Projective.FiniteGroupFacts.IcosahedralNormalizer
import Holant.Projective.FiniteGroupFacts.ActualIcosahedral

/-! All eight clauses of source Lemma 2.2 (finite projective-group facts).
The cyclic group is finite, as in the surrounding finite-group setting; the
dihedral parameter uses the source's preceding convention `2 ≤ m`.
The normalizers and projective centralizers live in the genuine quotient
`PGL2 ℂ`, and `modelPGL` is explicitly tied to the displayed matrix families. -/
namespace Holant.Projective.FiniteGroupFacts
open Holant.Projective.BoundedTorsion ProjectiveCentralizers
noncomputable section

structure CyclicClause (G : Type*) [Group G] : Prop where
  at_most_one : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x = y
  exists_iff_even : (∃ x : G, orderOf x = 2) ↔ Even (Nat.card G)
  subgroups : ∀ H : Subgroup G, IsCyclic H

structure DihedralClause (m : ℕ) : Prop where
  rotations_cyclic : IsCyclic (Dihedral.rotations m)
  rotations_isomorphism : Nonempty (Multiplicative (ZMod m) ≃* Dihedral.rotations m)
  rotations_normal : (Dihedral.rotations m).Normal
  rotations_index : (Dihedral.rotations m).index = 2
  reflections : ∀ x : DihedralGroup m, x ∉ Dihedral.rotations m →
    (∃ i, x = DihedralGroup.sr i) ∧ orderOf x = 2
  odd_unique_index_two : Odd m → ∀ H : Subgroup (DihedralGroup m),
    H.index = 2 → H = Dihedral.rotations m
  odd_center : Odd m → Subgroup.center (DihedralGroup m) = ⊥
  even_center : 4 ≤ m → Even m → ∀ x : DihedralGroup m,
    x ∈ Subgroup.center (DihedralGroup m) ↔ x = 1 ∨ x = DihedralGroup.r (m / 2 : ℕ)
  d4_isomorphism : Nonempty (DihedralGroup 2 ≃* Multiplicative (ZMod 2 × ZMod 2))
  d4_center : Subgroup.center (DihedralGroup 2) = ⊤
  d4_three_involutions : Fintype.card {x : DihedralGroup 2 // x ≠ 1} = 3 ∧
    ∀ x : DihedralGroup 2, x ≠ 1 → orderOf x = 2
  subgroups : ∀ H : Subgroup (DihedralGroup m),
    IsCyclic H ∨ ∃ k : ℕ, 2 ≤ k ∧ Nonempty (DihedralGroup k ≃* H)

structure TetrahedralClause : Prop where
  involutions : orderCount A4 2 = 3
  klein_members : ∀ g : A4, g ∈ a4KleinFour ↔ g = 1 ∨ Involution g
  klein_type : IsKleinFour a4KleinFour
  klein_normal : a4KleinFour.Normal
  klein_unique : ∀ H : Subgroup A4, IsKleinFour H → H = a4KleinFour
  no_index_two : ∀ H : Subgroup A4, H.index ≠ 2
  centralizers : ∀ g : A4, Involution g → Subgroup.centralizer {g} = a4KleinFour

structure OctahedralClause : Prop where
  alternating_index : (alternatingGroup (Fin 4)).index = 2
  unique_index_two : ∀ H : Subgroup S4, H.index = 2 → H = alternatingGroup (Fin 4)
  involution_types : ∀ g : S4, Involution g ↔ Transposition g ∨ DoubleTransposition g
  transpositions : ((Finset.univ : Finset S4).filter Transposition).card = 6
  double_transpositions : ((Finset.univ : Finset S4).filter DoubleTransposition).card = 3
  transposition_centralizer : ∀ g : S4, g.IsSwap → Nat.card (Subgroup.centralizer {g}) = 4
  double_centralizer : ∀ g : S4, DoubleTransposition g →
    Nonempty (DihedralGroup 4 ≃* Subgroup.centralizer {g})
  klein_members : ∀ g : S4, g ∈ s4KleinFour ↔ g = 1 ∨ DoubleTransposition g
  klein_type : IsKleinFour s4KleinFour
  klein_normal : s4KleinFour.Normal
  klein_unique : ∀ H : Subgroup S4, H.Normal → IsKleinFour H → H = s4KleinFour
  double_pairs : ∀ a b a' b' : S4,
    DoubleTransposition a → DoubleTransposition b → a ≠ b →
    DoubleTransposition a' → DoubleTransposition b' → a' ≠ b' →
    ∃ c : S4, c * a * c⁻¹ = a' ∧ c * b * c⁻¹ = b'
  disjoint_pairs : ∀ a b a' b' : S4,
    a.IsSwap → b.IsSwap → Equiv.Perm.Disjoint a b →
    a'.IsSwap → b'.IsSwap → Equiv.Perm.Disjoint a' b' →
    ∃ c : S4, c * a * c⁻¹ = a' ∧ c * b * c⁻¹ = b'

structure IcosahedralClause : Prop where
  simple : IsSimpleGroup A5
  no_index_two : ∀ H : Subgroup A5, H.index ≠ 2
  involutions : orderCount A5 2 = 15
  one_class : ∀ g h : A5, Involution g → Involution h → IsConj g h
  centralizers : ∀ g : A5, Involution g → IsKleinFour (Subgroup.centralizer {g})

structure OrderDistributionClause : Prop where
  tetrahedral : orderCount A4 1 = 1 ∧ orderCount A4 2 = 3 ∧ orderCount A4 3 = 8 ∧
    orderCount A4 4 = 0 ∧ orderCount A4 5 = 0
  octahedral : orderCount S4 1 = 1 ∧ orderCount S4 2 = 9 ∧ orderCount S4 3 = 8 ∧
    orderCount S4 4 = 6 ∧ orderCount S4 5 = 0
  icosahedral : orderCount A5 1 = 1 ∧ orderCount A5 2 = 15 ∧ orderCount A5 3 = 20 ∧
    orderCount A5 4 = 0 ∧ orderCount A5 5 = 24
  tetrahedral_exhaustive : ∀ g : A4, orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3
  octahedral_exhaustive : ∀ g : S4,
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 4
  icosahedral_exhaustive : ∀ g : A5,
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 ∨ orderOf g = 5

structure NormalizerClause : Prop where
  tetrahedral : Subgroup.normalizer (modelPGL .tetrahedral : Set (PGL2 ℂ)) = modelPGL .octahedral
  octahedral : Subgroup.normalizer (modelPGL .octahedral : Set (PGL2 ℂ)) = modelPGL .octahedral
  icosahedral : Subgroup.normalizer (modelPGL .icosahedral : Set (PGL2 ℂ)) = modelPGL .icosahedral

structure ProjectiveCentralizerClause : Prop where
  centralizer_z : (Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) : Set (PGL2 ℂ)) =
    diagonalClasses ∪ antidiagonalClasses
  disjoint_union : Disjoint diagonalClasses antidiagonalClasses
  z_involution : orderOf zClass = 2
  diagonal_unique : ∀ q : PGL2 ℂ, q ∈ diagonalClasses → orderOf q = 2 → q = zClass
  antidiagonal_involutions : ∀ a b : ℂˣ, orderOf (pglMk ℂ (antidiagonalGL a b)) = 2
  pauli_centralizer : Subgroup.centralizer (pauliSubgroup : Set (PGL2 ℂ)) = pauliSubgroup
  pauli_type : Nonempty (pauliSubgroup ≃* Multiplicative (ZMod 2 × ZMod 2))
  finite_torus_subgroups : ∀ H : Subgroup (PGL2 ℂ), Finite H → H ≤ diagonalTorus → IsCyclic H

/-- The complete compound source statement, with each of its eight clauses explicit. -/
structure Lemma22 (G : Type*) [Group G] (m : ℕ) : Prop where
  cyclic : CyclicClause G
  dihedral : DihedralClause m
  tetrahedral : TetrahedralClause
  octahedral : OctahedralClause
  icosahedral : IcosahedralClause
  distributions : OrderDistributionClause
  normalizers : NormalizerClause
  centralizers : ProjectiveCentralizerClause

/-- Source Lemma 2.2, with the finite setting and preceding `m ≥ 2` convention.
No projective-group classification, closure, or centralizer conclusion is assumed. -/
theorem finite_projective_group_facts (G : Type*) [Group G] [Finite G] [IsCyclic G]
    (m : ℕ) (hm : 2 ≤ m) : Lemma22 G m where
  cyclic := {
    at_most_one := fun _ _ hx hy => cyclic_involution_unique hx hy
    exists_iff_even := cyclic_exists_involution_iff_even
    subgroups := cyclic_subgroup_isCyclic }
  dihedral := {
    rotations_cyclic := inferInstance
    rotations_isomorphism := ⟨Dihedral.rotationsEquiv m⟩
    rotations_normal := Dihedral.rotations_normal m
    rotations_index := Dihedral.rotations_index m
    reflections := fun _ hx => Dihedral.outside_rotations hx
    odd_unique_index_two := Dihedral.odd_unique_index_two
    odd_center := Dihedral.odd_center hm
    even_center := Dihedral.even_center_membership
    d4_isomorphism := Dihedral.d4_equiv_kleinFour
    d4_center := Dihedral.d4_center
    d4_three_involutions := ⟨Dihedral.d4_three_nonidentity, fun _ h => Dihedral.d4_nonidentity_involutions h⟩
    subgroups := Dihedral.subgroup_cyclic_or_dihedral hm }
  tetrahedral := {
    involutions := a4_order_distribution.2.1
    klein_members := a4_mem_kleinFour
    klein_type := a4_kleinFour_isKleinFour
    klein_normal := a4_kleinFour_normal
    klein_unique := fun H h => @a4_unique_kleinFour H h
    no_index_two := a4_no_index_two
    centralizers := a4_involution_centralizer }
  octahedral := {
    alternating_index := s4_alternating_index_two
    unique_index_two := s4_unique_index_two
    involution_types := s4_involution_types
    transpositions := s4_transposition_count
    double_transpositions := s4_double_transposition_count
    transposition_centralizer := fun g hg => s4_transposition_centralizer_card g
      ((transposition_iff_isSwap g).mpr hg)
    double_centralizer := s4_double_centralizer_dihedral
    klein_members := s4_mem_kleinFour
    klein_type := s4_kleinFour_isKleinFour
    klein_normal := s4_kleinFour_normal
    klein_unique := fun H hN hK => @s4_unique_normal_kleinFour H hN hK
    double_pairs := s4_double_pairs_transitive
    disjoint_pairs := s4_disjoint_transposition_pairs_transitive }
  icosahedral := {
    simple := a5_simple
    no_index_two := a5_no_index_two
    involutions := a5_order_distribution.2.1
    one_class := a5_involutions_one_class
    centralizers := a5_involution_centralizer_kleinFour }
  distributions := {
    tetrahedral := a4_order_distribution
    octahedral := s4_order_distribution
    icosahedral := a5_order_distribution
    tetrahedral_exhaustive := a4_orders_exhaustive
    octahedral_exhaustive := s4_orders_exhaustive
    icosahedral_exhaustive := a5_orders_exhaustive }
  normalizers := {
    tetrahedral := tetrahedral_normalizer
    octahedral := octahedral_normalizer
    icosahedral := icosahedral_normalizer }
  centralizers := {
    centralizer_z := centralizer_z
    disjoint_union := diagonal_antidiagonal_disjoint
    z_involution := zClass_involution
    diagonal_unique := fun _ => diagonal_involution_unique
    antidiagonal_involutions := antidiagonal_involution
    pauli_centralizer := pauli_self_centralizer
    pauli_type := pauli_equiv_kleinFour
    finite_torus_subgroups := fun H hfin => @finite_diagonal_subgroup_isCyclic H hfin }

end
end Holant.Projective.FiniteGroupFacts
