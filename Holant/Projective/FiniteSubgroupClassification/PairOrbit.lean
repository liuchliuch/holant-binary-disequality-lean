import Holant.Projective.FiniteSubgroupClassification.DihedralConjugacy
import Holant.Projective.FiniteSubgroupClassification.Signatures

/-! A genuine two-point projective orbit gives actual standard dihedral
conjugacy for a finite noncyclic subgroup. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

theorem fixedPoints_zClass : fixedPoints zClass = {zeroPoint, infinityPoint} := by
  rw [← torus_neg_one]
  exact fixedPoints_torus (by norm_num)

/-- Preserving the two coordinate lines setwise is exactly centralizing `[Z]`. -/
theorem mem_centralizer_z_iff_preserves_pair (g : PGL2 ℂ) :
    g ∈ Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) ↔
      (fun p : ProjectiveLine => g • p) '' {zeroPoint, infinityPoint} =
        {zeroPoint, infinityPoint} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    rw [← fixedPoints_zClass, ← fixedPoints_conjugate]
    congr 1
    rw [hg]
    simp [mul_assoc]
  · intro hg
    have he : fixedPoints (g * zClass * g⁻¹) = {zeroPoint, infinityPoint} := by
      rw [fixedPoints_conjugate, fixedPoints_zClass, hg]
    have hfix : (g * zClass * g⁻¹) • zeroPoint = zeroPoint ∧
        (g * zClass * g⁻¹) • infinityPoint = infinityPoint := by
      constructor <;> change _ ∈ fixedPoints (g * zClass * g⁻¹) <;> rw [he] <;> simp
    have hd : g * zClass * g⁻¹ ∈ diagonalClasses := by
      rw [← diagonalTorus_carrier]
      exact fixes_coordinate_pair_iff_mem_torus.mp hfix
    have hz := diagonal_involution_unique hd
      ((MulAut.conj g).orderOf_eq zClass |>.trans zClass_involution)
    exact mul_inv_eq_iff_eq_mul.mp hz

/-- An invariant pair can be moved to the coordinate pair, putting the entire
subgroup into the actual diagonal/antidiagonal centralizer. -/
theorem invariant_pair_conjugate_centralizer (H : Subgroup (PGL2 ℂ))
    (a b : ProjectiveLine) (hab : a ≠ b)
    (hpair : ∀ q ∈ H, (fun p : ProjectiveLine => q • p) '' {a, b} = {a, b}) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  obtain ⟨g, hga, hgb⟩ := exists_smul_pair hab zeroPoint_ne_infinityPoint
  have him : (fun p : ProjectiveLine => g • p) '' {a, b} = {zeroPoint, infinityPoint} := by
    simp [hga, hgb]
  refine ⟨g, ?_⟩
  rintro q ⟨r, hr, rfl⟩
  apply (mem_centralizer_z_iff_preserves_pair _).mpr
  calc
    _ = (fun p : ProjectiveLine => g • p) '' ((fun p : ProjectiveLine => r • p) '' {a, b}) := by
      rw [← him, Set.image_image, Set.image_image]
      congr 1
      funext p
      simp [MulAut.conj_apply, mul_smul]
    _ = _ := by rw [hpair r hr, him]

/-- A two-point orbit forces conjugacy into the coordinate-pair stabilizer. -/
theorem two_point_orbit_conjugate_centralizer (H : Subgroup (PGL2 ℂ))
    (p : ProjectiveLine) (hcard : (MulAction.orbit H p).ncard = 2) :
    ∃ g : PGL2 ℂ, H.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ({zClass} : Set (PGL2 ℂ)) := by
  obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.mp hcard
  apply invariant_pair_conjugate_centralizer H a b hab
  intro q hq
  rw [← he]
  exact MulAction.smul_orbit (⟨q, hq⟩ : H) p

/-- The complete actual dihedral conclusion for the geometric two-point-orbit case. -/
theorem finite_two_point_orbit_dihedral_conjugacy
    (H : Subgroup (PGL2 ℂ)) [Finite H] (hnc : ¬IsCyclic H)
    (p : ProjectiveLine) (hcard : (MulAction.orbit H p).ncard = 2) :
    ∃ g : PGL2 ℂ, ∃ ω : ℂˣ, ∃ m : ℕ, 2 ≤ m ∧ IsPrimitiveRoot ω m ∧
      H.map (MulAut.conj g).toMonoidHom = dihedralModel ω ∧ Nat.card H = 2 * m := by
  obtain ⟨g, hg⟩ := two_point_orbit_conjugate_centralizer H p hcard
  let e := MulAut.conj g
  let H' := H.map e.toMonoidHom
  letI : Finite H' := Finite.of_equiv H
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toEquiv
  have hnc' : ¬IsCyclic H' := fun h => hnc
    ((Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).isCyclic.mpr h)
  obtain ⟨t, ω, m, hm, hω, he, hc⟩ := finite_centralizer_noncyclic_conjugacy H' hg hnc'
  refine ⟨torusHom t * g, ω, m, hm, hω, ?_, ?_⟩
  · have hcomp : (MulAut.conj (torusHom t * g)).toMonoidHom =
        (MulAut.conj (torusHom t)).toMonoidHom.comp e.toMonoidHom := by
      ext q
      dsimp [e]
      group
    rw [hcomp, ← Subgroup.map_map]
    exact he
  · exact (card_conjugate_subgroup H g).symm.trans hc

/-- Orbit-stabilizer turns an index-two point stabilizer into a genuine two-point orbit. -/
theorem orbit_ncard_two_of_card_eq_twice_stabilizer
    (H : Subgroup (PGL2 ℂ)) [Finite H] (p : ProjectiveLine)
    (hc : Nat.card H = 2 * Nat.card (MulAction.stabilizer H p)) :
    (MulAction.orbit H p).ncard = 2 := by
  change Nat.card (MulAction.orbit H p) = 2
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := MulAction.stabilizer H p))
  calc
    _ = Nat.card H := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H p)
    _ = _ := hc

/-- The full `(2,2,m)` geometric branch gives genuine conjugacy to the source's
standard dihedral model, with the same stabilizer parameter `m`. -/
theorem exceptional_22m_conjugacy (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hnc : ¬IsCyclic H) (e : Fin 3 ≃ ExceptionalOrbits H)
    (_h0 : stabilizerOrder H (e 0) = 2) (_h1 : stabilizerOrder H (e 1) = 2)
    (hcard : Nat.card H = 2 * stabilizerOrder H (e 2)) :
    ∃ g : PGL2 ℂ, ∃ ω : ℂˣ,
      IsPrimitiveRoot ω (stabilizerOrder H (e 2)) ∧
      H.map (MulAut.conj g).toMonoidHom = dihedralModel ω := by
  have hc : Nat.card H = 2 * Nat.card (MulAction.stabilizer H (e 2).out.val) := by
    simpa only [stabilizerOrder, exceptional_stabilizer_eq] using hcard
  obtain ⟨g, ω, m, _, hω, he, hm⟩ := finite_two_point_orbit_dihedral_conjugacy
    H hnc (e 2).out.val (orbit_ncard_two_of_card_eq_twice_stabilizer H _ hc)
  have hmr : m = stabilizerOrder H (e 2) := by omega
  exact ⟨g, ω, hmr ▸ hω, he⟩

end
end Holant.Projective.FiniteSubgroupClassification
