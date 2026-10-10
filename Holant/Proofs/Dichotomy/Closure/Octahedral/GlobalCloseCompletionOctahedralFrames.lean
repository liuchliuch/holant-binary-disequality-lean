import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralStandard
import Holant.Certificates.OctahedralSeparator.GroupMatrixInverses

/-! Coefficient extraction from the preserved marked-octahedral proof. All FOUR actual marked coefficient frames preserve
the two-sided condition. The essential Gram correction is produced from
the old sInverse_standard_certificate, not an arbitrary normalizer input.
These analytic matrices are never installed as physical binary gadgets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.TwoSidedCompleteness
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.ExactAutomorphisms
open scoped BigOperators Matrix

def frameS (f : Form) : Holant.Certificates.TetrahedralPreservers.BinaryMatrix := complexMatrix (sMatrix f)
def frameSinverse (f : Form) : Holant.Certificates.TetrahedralPreservers.BinaryMatrix := complexMatrix (sInverse f)

theorem frameS_product (f : Form) : frameS f = rowMatrix f*(rowMatrix f).transpose := by
  simp only [frameS,sMatrix,complexMatrix_mm,complexMatrix_mt,rowMatrix]

theorem frameSinverse_product (f : Form) :
    frameSinverse f = ((rowMatrix f)⁻¹).transpose*(rowMatrix f)⁻¹ := by
  simp only [frameSinverse,sInverse,complexMatrix_mm,complexMatrix_mt,
    complexMatrix_inverseConjugator,rowMatrix]

theorem frameS_inverses (f : Form) :
    frameS f*frameSinverse f = 1 ∧ frameSinverse f*frameS f = 1 := by
  have he : frameS f*frameSinverse f = 1 := by
    rw [frameS,frameSinverse,←complexMatrix_mm,sMatrix_sInverse,complexMatrix_q0]
  exact ⟨he,mul_eq_one_comm.mp he⟩

/-- The old exact certificate supplies the actual standard root index
0/1/12/17 and its nonzero scale, for these four specific frames. -/
theorem frameSinverse_direction (f : Form) : Direction 0 (frameSinverse f) := by
  rw [frameSinverse,sInverse_standard_certificate,complexMatrix_ms]
  have hk : Direction 0 (complexMatrix (OctahedralSeparator.standard (correctionIndex f))) := by
    simpa only [theta_zero] using Direction.standard 0 (correctionIndex f)
  exact hk.smul (embed_ne_zero (correctionScale_nonzero f))

theorem frameS_direction (f : Form) : Direction 0 (frameS f) := by
  have he : (frameSinverse f)⁻¹ = frameS f := Matrix.inv_eq_left_inv (frameS_inverses f).1
  rw [←he]
  exact direction_zero_inverse (frameSinverse_direction f)

def gramLeft (f : Form) : End := sandwich (frameS f) (frameSinverse f)
def gramRight (f : Form) : End := sandwich (frameSinverse f) (frameS f)

theorem gram_inverses (f : Form) : gramLeft f*gramRight f = 1 ∧ gramRight f*gramLeft f = 1 := by
  constructor
  · rw [gramLeft,gramRight,sandwich_comp,(frameS_inverses f).1,sandwich_one]
  · rw [gramLeft,gramRight,sandwich_comp,(frameS_inverses f).2,sandwich_one]

theorem gramLeft_safe (f : Form) : OneSided (Roots 0) (gramLeft f) :=
  sandwich_safe_zero (frameS_direction f) (frameSinverse_direction f)

theorem gramRight_safe (f : Form) : OneSided (Roots 0) (gramRight f) :=
  sandwich_safe_zero (frameSinverse_direction f) (frameS_direction f)

private theorem inverse_row_frameS (f : Form) :
    (rowMatrix f)⁻¹*frameS f = (rowMatrix f).transpose := by
  rw [frameS_product,←Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (rowMatrix_det f)),Matrix.one_mul]

private theorem frameSinverse_row (f : Form) :
    frameSinverse f*rowMatrix f = ((rowMatrix f)⁻¹).transpose := by
  rw [frameSinverse_product,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (rowMatrix_det f)),Matrix.mul_one]

/-- Exact double-chart identities. They explicitly retain the actual
J_Fr sharp and the old S=HH^T, rather than declaring E orthogonal. -/
theorem sharp_inverse_chart (f : Form) :
    sharp (inverseChartMatrix f) = chartMatrix f*gramLeft f := by
  rw [inverseChartMatrix,sharp_sandwich,chartMatrix,gramLeft,sandwich_comp,
    inverse_row_frameS,frameSinverse_row]

theorem sharp_chart (f : Form) :
    sharp (chartMatrix f) = gramRight f*inverseChartMatrix f := by
  rw [chartMatrix,sharp_sandwich,gramRight,inverseChartMatrix,sandwich_comp,
    frameSinverse_row,inverse_row_frameS]

theorem gram_from_double_chart (f : Form) :
    inverseChartMatrix f*sharp (inverseChartMatrix f) = gramLeft f := by
  rw [sharp_inverse_chart,←Matrix.mul_assoc,(chart_inverses f).1,Matrix.one_mul]

theorem sharp_conjugation (f : Form) (A : End) :
    sharp (chartMatrix f*A*inverseChartMatrix f) =
      chartMatrix f*(gramLeft f*sharp A*gramRight f)*inverseChartMatrix f := by
  rw [sharp_mul,sharp_mul,sharp_inverse_chart,sharp_chart]
  simp only [Matrix.mul_assoc]

/-- Two-way point dictionary transport, applied only to the same marked
roots. No coefficient-frame matrix is asserted to have a physical tree. -/
theorem conjugate_safe (f : Form) (A : End) (h : OneSided (Roots 0) A) :
    OneSided (Roots f) (chartMatrix f*A*inverseChartMatrix f) := by
  intro v hv
  obtain ⟨k,c,hc,rfl⟩ := (roots_iff f v).mp hv
  have hzero : inverseChartMatrix f *ᵥ (c • point f k) ∈ Roots 0 := by
    rw [Matrix.mulVec_smul,inverse_chart_point]
    exact (roots_iff 0 _).mpr ⟨k,c,hc,rfl⟩
  simp only [←Matrix.mulVec_mulVec]
  rcases h _ hzero with hz | hm
  · exact Or.inl (by rw [hz,Matrix.mulVec_zero])
  · obtain ⟨j,d,hd,he⟩ := (roots_iff 0 _).mp hm
    rw [he,Matrix.mulVec_smul,chart_point]
    exact Or.inr ((roots_iff f _).mpr ⟨j,d,hd,rfl⟩)

/-- The marked sharp half comes from actual standard sharp safety and
the produced normalizer corrections C,C^-1 on the same root dictionary. -/
theorem conjugate_twoSided (f : Form) (A : End) (h : TwoSided (Roots 0) A) :
    TwoSided (Roots f) (chartMatrix f*A*inverseChartMatrix f) := by
  refine ⟨conjugate_safe f A h.1,?_⟩
  rw [sharp_conjugation]
  apply conjugate_safe
  exact oneSided_comp (oneSided_comp (gramLeft_safe f) h.2) (gramRight_safe f)

theorem markedCandidate_twoSided (f : Form) (i : CandidateIndex) :
    TwoSided (Roots f) (markedCandidate f i) :=
  conjugate_twoSided f (standardCandidate i) (standardCandidate_twoSided i)

theorem markedCandidate_rank (f : Form) (i : CandidateIndex) :
    (markedCandidate f i).rank = 4 := by
  obtain ⟨U,W,hU,hW,he⟩ := markedCandidate_normal_forms f i 1 one_ne_zero
  simp only [one_smul] at he
  have cancel (M : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
      U⁻¹*(U*M*W)*W⁻¹=M := by
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv W (isUnit_iff_ne_zero.mpr hW),Matrix.mul_one]
    rw [←Matrix.mul_assoc,Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hU),Matrix.one_mul]
  have hi : Function.Injective (markedCandidate f i).mulVec := by
    intro x y h
    rcases he with he|he
    · rw [he,sandwich_action,sandwich_action] at h
      have hh := congrArg (fun M : Holant.Certificates.TetrahedralPreservers.BinaryMatrix=>U⁻¹*M*W⁻¹)
        (coordinates.injective h)
      have hx : assemble x=assemble y := by simpa only [cancel] using hh
      exact coordinates.symm.injective hx
    · rw [he,transposeSandwich_action,transposeSandwich_action] at h
      have hh := congrArg (fun M : Holant.Certificates.TetrahedralPreservers.BinaryMatrix=>U⁻¹*M*W⁻¹)
        (coordinates.injective h)
      have hx : (assemble x).transpose=(assemble y).transpose := by simpa only [cancel] using hh
      exact coordinates.symm.injective (Matrix.transpose_injective hx)
  rw [Matrix.rank,LinearMap.finrank_range_of_inj hi]
  simp


theorem pull_conjugate (f : Form) (A : End) :
    ExactAutomorphisms.pull f (chartMatrix f*A*inverseChartMatrix f)=A := by
  simp only [ExactAutomorphisms.pull,Matrix.mul_assoc]
  rw [(chart_inverses f).1,Matrix.mul_one]
  rw [←Matrix.mul_assoc,(chart_inverses f).1,Matrix.one_mul]

theorem pull_sharp (f : Form) (A : End) :
    ExactAutomorphisms.pull f (sharp A)=
      gramLeft f*sharp (ExactAutomorphisms.pull f A)*gramRight f := by
  have h := sharp_conjugation f (ExactAutomorphisms.pull f A)
  rw [unpull] at h
  rw [h,pull_conjugate]

/-- The reverse frame transport retains both explicit Gram corrections.
It is valid for singular maps as well as the full-rank candidates. -/
theorem pull_twoSided (f : Form) (A : End) (h : TwoSided (Roots f) A) :
    TwoSided (Roots 0) (ExactAutomorphisms.pull f A) := by
  refine ⟨pull_safe f A h.1,?_⟩
  have hs := oneSided_comp
    (oneSided_comp (gramRight_safe f) (pull_safe f (sharp A) h.2)) (gramLeft_safe f)
  rw [pull_sharp] at hs
  have eq : (gramRight f*(gramLeft f*sharp (ExactAutomorphisms.pull f A)*gramRight f))*gramLeft f=
      sharp (ExactAutomorphisms.pull f A) := by
    simp only [Matrix.mul_assoc]
    rw [(gram_inverses f).2,Matrix.mul_one]
    rw [←Matrix.mul_assoc,(gram_inverses f).2,Matrix.one_mul]
  rwa [eq] at hs

theorem pull_rank (f : Form) (A : End) : (ExactAutomorphisms.pull f A).rank=A.rank := by
  rw [ExactAutomorphisms.pull,
    Matrix.rank_mul_eq_left_of_det_ne_zero _ _ (chart_dets f).1,
    Matrix.rank_mul_eq_right_of_det_ne_zero _ _ (chart_dets f).2]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.TwoSidedCompleteness
