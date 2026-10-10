import Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The faithful action of the project's actual scalar quotient `PGL2 ℂ`
on the complex projective line. This bridge uses the same literal matrix
representatives as the displayed models. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
open scoped LinearAlgebra.Projectivization
noncomputable section

abbrev ProjectiveLine := ℙ ℂ (Bool → ℂ)

/-- Identifying the scalar quotient with Mathlib's center quotient. -/
def pglEquivMathlib : PGL2 ℂ ≃* Matrix.ProjGenLinGroup Bool ℂ :=
  QuotientGroup.quotientMulEquivOfEq
    Matrix.GeneralLinearGroup.center_eq_range_scalar.symm

@[simp] theorem pglEquivMathlib_mk (g : GL2C) :
    pglEquivMathlib (pglMk ℂ g) = Matrix.ProjGenLinGroup.mk g := rfl

instance : MulAction (PGL2 ℂ) ProjectiveLine :=
  MulAction.compHom ProjectiveLine pglEquivMathlib.toMonoidHom

@[simp] theorem pglMk_smul (g : GL2C) (p : ProjectiveLine) :
    pglMk ℂ g • p = g • p := rfl

@[simp] theorem pglMk_smul_mk (g : GL2C) (v : Bool → ℂ) (hv : v ≠ 0) :
    pglMk ℂ g • Projectivization.mk ℂ v hv =
      Projectivization.mk ℂ (g • v) ((smul_ne_zero_iff_ne g).mpr hv) := rfl

/-- The point represented by the first coordinate vector. -/
def zeroPoint : ProjectiveLine :=
  Projectivization.mk ℂ (fun b : Bool => if b then 0 else 1) (by
    intro h; have := congrFun h false; simp at this)

/-- The point represented by the second coordinate vector. -/
def infinityPoint : ProjectiveLine :=
  Projectivization.mk ℂ (fun b : Bool => if b then 1 else 0) (by
    intro h; have := congrFun h true; simp at this)

/-- The point represented by the sum of the coordinate vectors. -/
def onePoint : ProjectiveLine :=
  Projectivization.mk ℂ (fun _ : Bool => 1) (by
    intro h; have := congrFun h false; simp at this)

theorem zeroPoint_ne_infinityPoint : zeroPoint ≠ infinityPoint := by
  intro h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).mp h
  have := congrFun hc false
  simp at this

/-- Two distinct projective points can be sent to any two others by an actual
matrix representative, then by its class in the project's quotient. -/
theorem exists_smul_pair {a b c d : ProjectiveLine} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : PGL2 ℂ, g • a = c ∧ g • b = d := by
  have ht : MulAction.IsMultiplyPretransitive
      (Matrix.SpecialLinearGroup Bool ℂ) ProjectiveLine 2 := inferInstance
  obtain ⟨g, hg, hg'⟩ := MulAction.is_two_pretransitive_iff.mp ht hab hcd
  exact ⟨pglMk ℂ (Matrix.SpecialLinearGroup.toGL g), hg, hg'⟩

/-- Fixing both coordinate points is precisely the diagonal matrix condition. -/
theorem fixes_coordinate_pair_iff {g : GL2C} :
    (pglMk ℂ g • zeroPoint = zeroPoint ∧
      pglMk ℂ g • infinityPoint = infinityPoint) ↔
      g false true = 0 ∧ g true false = 0 := by
  simp only [zeroPoint, infinityPoint, pglMk_smul_mk,
    Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h10 := congrFun ha true
    have h01 := congrFun hb false
    constructor
    · simpa [Units.smul_def, Matrix.mulVec, dotProduct] using h01.symm
    · simpa [Units.smul_def, Matrix.mulVec, dotProduct] using h10.symm
  · rintro ⟨h01, h10⟩
    obtain ⟨a, b, rfl⟩ := diagonal_form g h01 h10
    constructor
    · refine ⟨a, ?_⟩
      funext i
      cases i <;> simp [Units.smul_def, diagonalGL, diagonal, Matrix.mulVec, dotProduct]
    · refine ⟨b, ?_⟩
      funext i
      cases i <;> simp [Units.smul_def, diagonalGL, diagonal, Matrix.mulVec, dotProduct]

/-- The pointwise stabilizer of the two coordinate points is the diagonal torus. -/
theorem fixes_coordinate_pair_iff_mem_torus {g : PGL2 ℂ} :
    (g • zeroPoint = zeroPoint ∧ g • infinityPoint = infinityPoint) ↔
      g ∈ diagonalTorus := by
  induction g using Quotient.inductionOn with
  | h g =>
    change (pglMk ℂ g • zeroPoint = zeroPoint ∧
      pglMk ℂ g • infinityPoint = infinityPoint) ↔ pglMk ℂ g ∈ diagonalTorus
    rw [fixes_coordinate_pair_iff]
    constructor
    · rintro ⟨h01, h10⟩
      obtain ⟨a, b, rfl⟩ := diagonal_form g h01 h10
      exact ⟨a * b⁻¹, (diagonal_normalize a b).symm⟩
    · intro h
      have : pglMk ℂ g ∈ diagonalClasses := by rwa [← diagonalTorus_carrier]
      obtain ⟨a, b, he⟩ := this
      have hfix : pglMk ℂ (diagonalGL a b) • zeroPoint = zeroPoint ∧
          pglMk ℂ (diagonalGL a b) • infinityPoint = infinityPoint :=
        fixes_coordinate_pair_iff.mpr (by simp [diagonalGL, diagonal])
      exact fixes_coordinate_pair_iff.mp (he.symm ▸ hfix)

/-- A representative lies on the first coordinate line exactly when its second
coordinate vanishes. -/
theorem mk_eq_zeroPoint_iff (v : Bool → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv = zeroPoint ↔ v true = 0 := by
  rw [zeroPoint, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have := congrFun ha true
    simpa using this.symm
  · intro ht
    have hf : v false ≠ 0 := by
      intro hf
      apply hv
      funext i
      cases i <;> simp [hf, ht]
    refine ⟨Units.mk0 (v false) hf, ?_⟩
    funext i
    cases i <;> simp [ht]

/-- The analogous coordinate test for the second line. -/
theorem mk_eq_infinityPoint_iff (v : Bool → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv = infinityPoint ↔ v false = 0 := by
  rw [infinityPoint, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have := congrFun ha false
    simpa using this.symm
  · intro hf
    have ht : v true ≠ 0 := by
      intro ht
      apply hv
      funext i
      cases i <;> simp [hf, ht]
    refine ⟨Units.mk0 (v true) ht, ?_⟩
    funext i
    cases i <;> simp [hf]

/-- A nonidentity diagonal projective transformation fixes exactly the two
coordinate lines. -/
theorem torus_fixed_iff {a : ℂˣ} (ha : a ≠ 1) (p : ProjectiveLine) :
    torusHom a • p = p ↔ p = zeroPoint ∨ p = infinityPoint := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [mk_eq_zeroPoint_iff, mk_eq_infinityPoint_iff]
    change pglMk ℂ (diagonalGL a 1) • Projectivization.mk ℂ v hv = _ ↔ _
    rw [pglMk_smul_mk, Projectivization.mk_eq_mk_iff]
    constructor
    · rintro ⟨c, hc⟩
      have h0 := congrFun hc false
      have h1 := congrFun hc true
      simp [Units.smul_def, diagonalGL, diagonal, Matrix.mulVec, dotProduct] at h0 h1
      by_cases hv0 : v false = 0
      · exact Or.inr hv0
      · left
        by_contra hv1
        have hc1 : (c : ℂ) = 1 := (mul_eq_right₀ hv1).mp h1
        have hca : (c : ℂ) = (a : ℂ) := h0.resolve_right hv0
        exact ha (Units.ext (hca.symm.trans hc1))
    · rintro (ht | hf)
      · refine ⟨a, ?_⟩
        funext i
        cases i <;> simp [Units.smul_def, diagonalGL, diagonal, Matrix.mulVec, dotProduct, ht]
      · refine ⟨1, ?_⟩
        funext i
        cases i <;> simp [Units.smul_def, diagonalGL, diagonal, Matrix.mulVec, dotProduct, hf]

/-- A projective transformation fixing the three standard points is trivial. -/
theorem eq_one_of_fixes_three {g : PGL2 ℂ}
    (h0 : g • zeroPoint = zeroPoint) (hi : g • infinityPoint = infinityPoint)
    (h1 : g • onePoint = onePoint) : g = 1 := by
  obtain ⟨a, rfl⟩ := fixes_coordinate_pair_iff_mem_torus.mp ⟨h0, hi⟩
  by_cases ha : a = 1
  · simp [ha]
  · have hp := (torus_fixed_iff ha onePoint).mp h1
    rcases hp with hp | hp
    · have := (mk_eq_zeroPoint_iff (fun _ : Bool => (1 : ℂ)) _).mp hp
      norm_num at this
    · have := (mk_eq_infinityPoint_iff (fun _ : Bool => (1 : ℂ)) _).mp hp
      norm_num at this

instance : FaithfulSMul (PGL2 ℂ) ProjectiveLine :=
  faithfulSMul_iff.mpr fun g hg => eq_one_of_fixes_three (hg _) (hg _) (hg _)

end
end Holant.Projective.FiniteSubgroupClassification
