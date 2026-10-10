import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralCandidates

/-! Coefficient extraction from the preserved marked-octahedral proof. All four actual marked rows are transported through
their old coordinate dictionary. Both input/output coefficient operators
are explicit inverses; no analytic conjugator is declared to be a gadget.
Transpose factors retain their distinct left/right inverse-transpose terms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open scoped BigOperators Matrix

def rowMatrix (f : Form) : Holant.Certificates.TetrahedralPreservers.BinaryMatrix := complexMatrix (conjugator f)
def chartMatrix (f : Form) : End := sandwich (rowMatrix f)⁻¹ (rowMatrix f)
def inverseChartMatrix (f : Form) : End := sandwich (rowMatrix f) (rowMatrix f)⁻¹

theorem rowMatrix_det (f : Form) : (rowMatrix f).det ≠ 0 :=
  complexMatrix_conjugator_det_ne_zero f

theorem chart_inverses (f : Form) :
    inverseChartMatrix f*chartMatrix f = 1 ∧ chartMatrix f*inverseChartMatrix f = 1 := by
  constructor
  · rw [inverseChartMatrix,chartMatrix,sandwich_comp,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (rowMatrix_det f)),sandwich_one]
  · rw [inverseChartMatrix,chartMatrix,sandwich_comp,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (rowMatrix_det f)),sandwich_one]

theorem chart_dets (f : Form) :
    (chartMatrix f).det ≠ 0 ∧ (inverseChartMatrix f).det ≠ 0 := by
  have hn : (inverseChartMatrix f).det*(chartMatrix f).det ≠ 0 := by
    rw [←Matrix.det_mul,(chart_inverses f).1,Matrix.det_one]
    exact one_ne_zero
  exact ⟨(mul_ne_zero_iff.mp hn).2,(mul_ne_zero_iff.mp hn).1⟩

theorem chart_action (f : Form) (v : V) : chartMatrix f *ᵥ v = chart f v := by
  rw [chartMatrix,sandwich_action]
  change coordinates ((rowMatrix f)⁻¹*assemble v*rowMatrix f) =
    coordinates ((rowMatrix f)⁻¹*(assemble v*rowMatrix f))
  rw [Matrix.mul_assoc]

theorem chart_point (f : Form) (k : Fin 24) :
    chartMatrix f *ᵥ point 0 k = point f k := by
  have h0 : point 0 k = coordinates (complexMatrix (OctahedralSeparator.standard k)) := by
    rw [point_zero_representative]
    change coordinates (goldenMatrix (octahedralRaw k)) = _
    rw [octahedralRaw_standard]
  rw [chart_action,h0,←point_chart]

theorem inverse_chart_point (f : Form) (k : Fin 24) :
    inverseChartMatrix f *ᵥ point f k = point 0 k := by
  rw [←chart_point f k,Matrix.mulVec_mulVec,(chart_inverses f).1,Matrix.one_mulVec]

def pull (f : Form) (A : End) : End := inverseChartMatrix f*A*chartMatrix f

theorem pull_det (f : Form) (A : End) (hd : A.det ≠ 0) : (pull f A).det ≠ 0 := by
  rw [pull,Matrix.det_mul,Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (chart_dets f).2 hd) (chart_dets f).1

theorem pull_safe (f : Form) (A : End) (h : OneSided (Roots f) A) :
    OneSided (Roots 0) (pull f A) := by
  intro v hv
  obtain ⟨k,c,hc,rfl⟩ := (roots_iff 0 v).mp hv
  have hfv : chartMatrix f *ᵥ (c • point 0 k) ∈ Roots f := by
    rw [Matrix.mulVec_smul,chart_point]
    exact (roots_iff f _).mpr ⟨k,c,hc,rfl⟩
  simp only [pull,←Matrix.mulVec_mulVec]
  rcases h _ hfv with hz | hm
  · exact Or.inl (by rw [hz,Matrix.mulVec_zero])
  · obtain ⟨j,d,hd,he⟩ := (roots_iff f _).mp hm
    rw [he,Matrix.mulVec_smul,inverse_chart_point]
    exact Or.inr ((roots_iff 0 _).mpr ⟨j,d,hd,rfl⟩)

theorem unpull (f : Form) (A : End) : chartMatrix f*pull f A*inverseChartMatrix f = A := by
  calc
    chartMatrix f*pull f A*inverseChartMatrix f =
        (chartMatrix f*inverseChartMatrix f)*A*(chartMatrix f*inverseChartMatrix f) := by
      simp only [pull,Matrix.mul_assoc]
    _ = A := by rw [(chart_inverses f).2,Matrix.one_mul,Matrix.mul_one]

def markedCandidate (f : Form) (i : CandidateIndex) : End :=
  chartMatrix f*standardCandidate i*inverseChartMatrix f

theorem marked_candidate_coverage (f : Form) (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots f) A) :
    ∃ i : CandidateIndex, ∃ c : ℂ, c ≠ 0 ∧ A = c • markedCandidate f i := by
  obtain ⟨i,c,hc,he⟩ := candidate_coverage (pull f A) (pull_det f A hd) (pull_safe f A h)
  refine ⟨i,c,hc,?_⟩
  calc
    A = chartMatrix f*pull f A*inverseChartMatrix f := (unpull f A).symm
    _ = c • markedCandidate f i := by
      rw [he,Matrix.mul_smul,Matrix.smul_mul]
      rfl

theorem transpose_sandwich_comp (U W V Z : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    transposeSandwich U W*sandwich V Z =
      transposeSandwich (U*Z.transpose) (V.transpose*W) := by
  apply matrix_ext_action
  intro v
  rw [←Matrix.mulVec_mulVec,sandwich_action,transposeSandwich_action,transposeSandwich_action]
  change coordinates (U*(assemble (quaternionCoefficient (V*assemble v*Z))).transpose*W) = _
  rw [assemble_coefficient]
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

private theorem conjugate_normal_forms (f : Form) (A : End)
    (U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) (hU : U.det ≠ 0) (hW : W.det ≠ 0)
    (he : A = sandwich U W ∨ A = transposeSandwich U W) :
    ∃ V Z : Holant.Certificates.TetrahedralPreservers.BinaryMatrix, V.det ≠ 0 ∧ Z.det ≠ 0 ∧
      (chartMatrix f*A*inverseChartMatrix f = sandwich V Z ∨
        chartMatrix f*A*inverseChartMatrix f = transposeSandwich V Z) := by
  rcases he with he | he
  · refine ⟨(rowMatrix f)⁻¹*U*rowMatrix f,(rowMatrix f)⁻¹*W*rowMatrix f,?_,?_,Or.inl ?_⟩
    · rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero (rowMatrix_det f)) hU) (rowMatrix_det f)
    · rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero (rowMatrix_det f)) hW) (rowMatrix_det f)
    · rw [he,chartMatrix,inverseChartMatrix,sandwich_comp,sandwich_comp]
      simp only [Matrix.mul_assoc]
  · refine ⟨(rowMatrix f)⁻¹*U*((rowMatrix f)⁻¹).transpose,
      (rowMatrix f).transpose*W*rowMatrix f,?_,?_,Or.inr ?_⟩
    · simp only [Matrix.det_mul,Matrix.det_transpose,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
      exact mul_ne_zero (mul_ne_zero (inv_ne_zero (rowMatrix_det f)) hU)
        (inv_ne_zero (rowMatrix_det f))
    · simp only [Matrix.det_mul,Matrix.det_transpose]
      exact mul_ne_zero (mul_ne_zero (rowMatrix_det f) hW) (rowMatrix_det f)
    · rw [he,chartMatrix,inverseChartMatrix]
      have hh : sandwich (rowMatrix f)⁻¹ (rowMatrix f)*transposeSandwich U W =
          transposeSandwich ((rowMatrix f)⁻¹*U) (W*rowMatrix f) :=
        sandwich_kind_comp true _ _ _ _
      rw [hh,transpose_sandwich_comp]
      simp only [Matrix.mul_assoc]

/-- Exact forms for an arbitrary complex map in any actual fixed row.
Only the produced root-preserver property and actual determinant are used. -/
theorem marked_normal_forms (f : Form) (A : End) (hd : A.det ≠ 0)
    (h : OneSided (Roots f) A) :
    ∃ U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (A = sandwich U W ∨ A = transposeSandwich U W) := by
  obtain ⟨U,W,hU,hW,he⟩ := standard_full_rank_normal_forms
    (pull f A) (pull_det f A hd) (pull_safe f A h)
  simpa only [unpull] using conjugate_normal_forms f (pull f A) U W hU hW he

/-- Explicit reconstruction for EACH of the 24*24*2 slots in each of
the four old marked rows, including the produced scale. -/
theorem markedCandidate_normal_forms (f : Form) (i : CandidateIndex) (c : ℂ) (hc : c ≠ 0) :
    ∃ U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix, U.det ≠ 0 ∧ W.det ≠ 0 ∧
      (c • markedCandidate f i = sandwich U W ∨
        c • markedCandidate f i = transposeSandwich U W) := by
  obtain ⟨U,W,hU,hW,he⟩ := standardCandidate_normal_forms i c hc
  simpa only [markedCandidate,Matrix.mul_smul,Matrix.smul_mul] using
    conjugate_normal_forms f (c • standardCandidate i) U W hU hW he

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
