import Holant.Projective.FiniteSubgroupClassification.Action
import Holant.Projective.FiniteSubgroupClassification.TorsionEigenvalues
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Data.Set.Card

/-! Every nonidentity finite-order projective transformation has exactly two
fixed points. The proof passes through the distinct characteristic roots of
its literal representative and genuine conjugation into the diagonal torus. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Distinct characteristic roots provide two distinct projective fixed points. -/
theorem exists_two_fixed_points {q : PGL2 ℂ} (hfin : IsOfFinOrder q) (hne : q ≠ 1) :
    ∃ p r : ProjectiveLine, p ≠ r ∧ q • p = p ∧ q • r = r := by
  induction q using Quotient.inductionOn with
  | h g =>
    obtain ⟨a, b, ha, hb, hab, _, _, hae, hbe⟩ := exists_distinct_eigenpair g hfin hne
    let f : Module.End ℂ (Bool → ℂ) := Matrix.toLinAlgEquiv' (g : Mat)
    have haspec : a ∈ spectrum ℂ f := by
      simpa only [f, AlgEquiv.spectrum_eq] using hae
    have hbspec : b ∈ spectrum ℂ f := by
      simpa only [f, AlgEquiv.spectrum_eq] using hbe
    obtain ⟨v, hv⟩ := (Module.End.HasEigenvalue.of_mem_spectrum haspec).exists_hasEigenvector
    obtain ⟨w, hw⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hbspec).exists_hasEigenvector
    refine ⟨Projectivization.mk ℂ v hv.2, Projectivization.mk ℂ w hw.2, ?_, ?_, ?_⟩
    · intro he
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp he
      have hvb : v ∈ f.eigenspace b := by
        rw [← hc]
        exact (f.eigenspace b).smul_mem (c : ℂ) hw.1
      exact hv.2 ((Submodule.disjoint_def.mp (f.disjoint_genEigenspace hab 1 1)) v hv.1 hvb)
    · change pglMk ℂ g • Projectivization.mk ℂ v hv.2 = Projectivization.mk ℂ v hv.2
      rw [pglMk_smul_mk, Projectivization.mk_eq_mk_iff]
      exact ⟨Units.mk0 a ha, hv.apply_eq_smul.symm⟩
    · change pglMk ℂ g • Projectivization.mk ℂ w hw.2 = Projectivization.mk ℂ w hw.2
      rw [pglMk_smul_mk, Projectivization.mk_eq_mk_iff]
      exact ⟨Units.mk0 b hb, hw.apply_eq_smul.symm⟩

/-- A nonidentity finite-order class is conjugate into the actual diagonal torus. -/
theorem exists_conjugate_torus {q : PGL2 ℂ} (hfin : IsOfFinOrder q) (hne : q ≠ 1) :
    ∃ g : PGL2 ℂ, ∃ a : ℂˣ, a ≠ 1 ∧ g * q * g⁻¹ = torusHom a := by
  obtain ⟨p, r, hpr, hp, hr⟩ := exists_two_fixed_points hfin hne
  obtain ⟨g, hg, hgr⟩ := exists_smul_pair hpr zeroPoint_ne_infinityPoint
  have hfix (x y : ProjectiveLine) (hxy : g • x = y) (hx : q • x = x) :
      (g * q * g⁻¹) • y = y := by
    rw [← hxy, mul_smul, mul_smul, inv_smul_smul, hx]
  obtain ⟨a, ha⟩ := fixes_coordinate_pair_iff_mem_torus.mp
    ⟨hfix p zeroPoint hg hp, hfix r infinityPoint hgr hr⟩
  refine ⟨g, a, ?_, ha.symm⟩
  intro ha1
  apply hne
  have he : g * q * g⁻¹ = 1 := by simpa [ha1] using ha.symm
  have := congrArg (fun x : PGL2 ℂ => g⁻¹ * x * g) he
  simpa [mul_assoc] using this

/-- The actual set of projective fixed points. -/
def fixedPoints (q : PGL2 ℂ) : Set ProjectiveLine := {p | q • p = p}

/-- The fixed set of a nonidentity diagonal class is exactly the coordinate pair. -/
theorem fixedPoints_torus {a : ℂˣ} (ha : a ≠ 1) :
    fixedPoints (torusHom a) = {zeroPoint, infinityPoint} := by
  ext p
  exact torus_fixed_iff ha p

/-- Conjugation carries fixed points by the same projective transformation. -/
theorem fixedPoints_conjugate (g q : PGL2 ℂ) :
    fixedPoints (g * q * g⁻¹) = (fun p : ProjectiveLine => g • p) '' fixedPoints q := by
  ext p
  constructor
  · intro hp
    refine ⟨g⁻¹ • p, ?_, by simp⟩
    change q • (g⁻¹ • p) = g⁻¹ • p
    have h := congrArg (fun x : ProjectiveLine => g⁻¹ • x) hp
    simpa only [mul_smul, inv_smul_smul] using h
  · rintro ⟨r, hr, rfl⟩
    change (g * q * g⁻¹) • (g • r) = g • r
    simpa only [mul_smul, inv_smul_smul] using congrArg (fun x : ProjectiveLine => g • x) hr

/-- The fixed set is finite, with no assumption that the projective line is finite. -/
theorem fixedPoints_finite {q : PGL2 ℂ} (hfin : IsOfFinOrder q) (hne : q ≠ 1) :
    (fixedPoints q).Finite := by
  obtain ⟨g, a, ha, he⟩ := exists_conjugate_torus hfin hne
  have himage : ((fun p : ProjectiveLine => g • p) '' fixedPoints q).Finite := by
    rw [← fixedPoints_conjugate, he, fixedPoints_torus ha]
    exact Set.toFinite _
  exact Set.Finite.of_finite_image himage (MulAction.injective g).injOn

/-- Exactly two fixed points for every nonidentity finite-order Möbius class. -/
theorem fixedPoints_ncard {q : PGL2 ℂ} (hfin : IsOfFinOrder q) (hne : q ≠ 1) :
    (fixedPoints q).ncard = 2 := by
  obtain ⟨g, a, ha, he⟩ := exists_conjugate_torus hfin hne
  rw [← Set.ncard_image_of_injective (fixedPoints q) (MulAction.injective g),
    ← fixedPoints_conjugate, he, fixedPoints_torus ha]
  simp [zeroPoint_ne_infinityPoint]

end
end Holant.Projective.FiniteSubgroupClassification
