import Holant.Projective.FiniteSubgroupClassification.Action
import Holant.Projective.FiniteSubgroupClassification.TorsionEigenvalues

/-! Finite point stabilizers in the actual projective-line action are cyclic.
The proof uses the faithful diagonal-ratio character of a finite triangular
subgroup; the kernel would consist of projective unipotents, which have infinite
order unless trivial in characteristic zero. -/

namespace Holant.Projective.FiniteSubgroupClassification
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

/-- The diagonal-entry ratio is invariant under scalar representatives. -/
def diagonalRatio : PGL2 ℂ → ℂ :=
  Quotient.lift (fun g : GL2C => g false false / g true true) (by
    intro g h he
    obtain ⟨c, hc, hscale⟩ := projectiveClass_eq_iff.mp
      (pglMk_eq_iff_projectiveClass_eq.mp (Quotient.sound he))
    have h00 := congrArg (fun M : Mat => M false false) hscale
    have h11 := congrArg (fun M : Mat => M true true) hscale
    simp only [Matrix.smul_apply, smul_eq_mul] at h00 h11
    rw [h00, h11]
    exact mul_div_mul_left _ _ hc)

@[simp] theorem diagonalRatio_mk (g : GL2C) :
    diagonalRatio (pglMk ℂ g) = g false false / g true true := rfl

/-- An upper triangular invertible matrix has nonzero diagonal entries. -/
theorem triangular_diagonal_ne_zero (g : GL2C) (h10 : g true false = 0) :
    g false false ≠ 0 ∧ g true true ≠ 0 := by
  have h0 := congrArg (fun M : Mat => M false false) g.inv_val
  have h1 := congrArg (fun M : Mat => M true true) g.val_inv
  simp [Matrix.mul_apply, h10] at h0 h1
  exact ⟨fun h => by simp [h] at h0, fun h => by simp [h] at h1⟩

/-- Fixing the first coordinate point is the upper triangular condition. -/
theorem fixes_zeroPoint_iff {g : GL2C} :
    pglMk ℂ g • zeroPoint = zeroPoint ↔ g true false = 0 := by
  simp only [zeroPoint, pglMk_smul_mk, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have := congrFun ha true
    simpa [Units.smul_def, Matrix.mulVec, dotProduct] using this.symm
  · intro h10
    refine ⟨Units.mk0 (g false false) (triangular_diagonal_ne_zero g h10).1, ?_⟩
    funext i
    cases i <;> simp [Units.smul_def, Matrix.mulVec, dotProduct, h10]

theorem diagonalRatio_mul {g h : PGL2 ℂ}
    (hg : g • zeroPoint = zeroPoint) (hh : h • zeroPoint = zeroPoint) :
    diagonalRatio (g * h) = diagonalRatio g * diagonalRatio h := by
  induction g using Quotient.inductionOn with
  | h g =>
    induction h using Quotient.inductionOn with
    | h h =>
      have hg10 := fixes_zeroPoint_iff.mp hg
      have hh10 := fixes_zeroPoint_iff.mp hh
      change diagonalRatio (pglMk ℂ g * pglMk ℂ h) =
        diagonalRatio (pglMk ℂ g) * diagonalRatio (pglMk ℂ h)
      rw [← map_mul, diagonalRatio_mk, diagonalRatio_mk, diagonalRatio_mk]
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, hg10, hh10, mul_div_mul_comm]

/-- The diagonal-ratio character of the stabilizer of the first point. -/
def stabilizerCharacter : MulAction.stabilizer (PGL2 ℂ) zeroPoint →* ℂ where
  toFun g := diagonalRatio g
  map_one' := by change (1 : ℂ) / 1 = 1; simp
  map_mul' g h := diagonalRatio_mul g.property h.property

/-- A finite-order upper triangular projective class in the kernel of the
character is the identity. -/
theorem eq_one_of_fixes_zeroPoint_of_ratio_one {g : PGL2 ℂ}
    (hfin : IsOfFinOrder g) (hfix : g • zeroPoint = zeroPoint)
    (hratio : diagonalRatio g = 1) : g = 1 := by
  induction g using Quotient.inductionOn with
  | h g =>
    have h10 := fixes_zeroPoint_iff.mp hfix
    have hdiag := triangular_diagonal_ne_zero g h10
    have he : g false false = g true true :=
      (div_eq_one_iff_eq hdiag.2).mp hratio
    have htr : Matrix.trace (g : Mat) = g false false + g false false := by
      simp [Matrix.trace, he]
    have hdet : Matrix.det (g : Mat) = g false false * g false false := by
      rw [← Matrix.det_reindex_self finTwoEquiv.symm (g : Mat), Matrix.det_fin_two]
      change g false false * g true true - g false true * g true false = _
      rw [h10, he]
      ring
    have hs := scalar_of_repeated_roots
      ((isOfFinOrder_pglMk_iff g).mp hfin) hdiag.1 htr hdet
    change pglMk ℂ g = pglMk ℂ 1
    exact pglMk_eq_iff_projectiveClass_eq.mpr
      (projectiveClass_eq_iff.mpr ⟨g false false, hdiag.1, hs⟩)

/-- Every finite subgroup fixing the first coordinate point is cyclic. -/
theorem finite_subgroup_fixing_zero_isCyclic (H : Subgroup (PGL2 ℂ)) [Finite H]
    (hH : ∀ g ∈ H, g • zeroPoint = zeroPoint) : IsCyclic H := by
  let f : H →* ℂ := stabilizerCharacter.comp
    (Subgroup.inclusion (show H ≤ MulAction.stabilizer (PGL2 ℂ) zeroPoint from hH))
  apply isCyclic_of_injective_ringHom f
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  apply eq_one_of_fixes_zeroPoint_of_ratio_one
  · exact (Subtype.val_injective.isOfFinOrder_iff (f := H.subtype)).mpr
      (isOfFinOrder_of_finite g)
  · exact hH g g.property
  · exact hg

/-- Any point can be moved to the first coordinate point. -/
theorem exists_smul_to_zero (p : ProjectiveLine) :
    ∃ g : PGL2 ℂ, g • p = zeroPoint := by
  by_cases hp : p = zeroPoint
  · exact ⟨1, by simpa using hp⟩
  · obtain ⟨g, hg, _⟩ := exists_smul_pair hp zeroPoint_ne_infinityPoint
    exact ⟨g, hg⟩

/-- Every finite subgroup of the projective group fixing a projective point is cyclic. -/
theorem finite_subgroup_fixing_point_isCyclic (H : Subgroup (PGL2 ℂ)) [Finite H]
    (p : ProjectiveLine) (hH : ∀ q ∈ H, q • p = p) : IsCyclic H := by
  obtain ⟨g, hg⟩ := exists_smul_to_zero p
  let e := MulAut.conj g
  let H' := H.map e.toMonoidHom
  have hfix : ∀ q ∈ H', q • zeroPoint = zeroPoint := by
    rintro q ⟨r, hr, rfl⟩
    change (g * r * g⁻¹) • zeroPoint = zeroPoint
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hH r hr]
  letI : Finite H' := Finite.of_equiv H
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toEquiv
  have hc : IsCyclic H' := finite_subgroup_fixing_zero_isCyclic H' hfix
  exact (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).isCyclic.mpr hc

/-- Point stabilizers inside arbitrary finite projective subgroups are cyclic. -/
theorem finite_point_stabilizer_isCyclic (H : Subgroup (PGL2 ℂ)) [Finite H]
    (p : ProjectiveLine) : IsCyclic (MulAction.stabilizer H p) := by
  let S := MulAction.stabilizer H p
  let T := S.map H.subtype
  have hT : ∀ q ∈ T, q • p = p := by
    rintro q ⟨r, hr, rfl⟩
    exact hr
  letI : Finite T := Finite.of_equiv S
    (Subgroup.equivMapOfInjective S H.subtype Subtype.val_injective).toEquiv
  have hc : IsCyclic T := finite_subgroup_fixing_point_isCyclic T p hT
  exact (Subgroup.equivMapOfInjective S H.subtype Subtype.val_injective).isCyclic.mpr hc

end
end Holant.Projective.FiniteSubgroupClassification
