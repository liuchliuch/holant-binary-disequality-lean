import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralCurrent
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralConditions
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralClassifier
import Holant.Proofs.Algorithms.PrimalityInterfaces

/-! Coefficient extraction from the preserved marked-octahedral proof. Genuine rank-zero/one reconstruction on the SAME q4.
These lemmas hold for arbitrary complex q4 tensors and do not assume a
finite normal-form catalogue, a full-rank map, or an octahedral terminal.
Ranks two, three and four remain separate unresolved S4 cases. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.Projective.BoundedTorsion
open Holant.Pauli.ExoticKlein.Fiber
open scoped BigOperators Matrix

/-- The original physical Pauli axes belong to every marked S4 form.
For Q3 this consumes the already proved fixed z-coordinate receipt, not
an arbitrary conjugating matrix declared to be an actual gadget. -/
theorem direction_quaternion (f : Form) (i : Fin 4) :
    Direction f (Matrix.of (quaternionBasis i)) := by
  have h0 : Direction f (complexMatrix (q 0)) := by
    rw [direction_iff_source_pull,←complexMatrix_pull]
    have hh : pull f (q 0) = q 0 := by
      simp only [pull,q0_mm]
      exact (conjugator_inverses f).1
    rw [hh,complexMatrix_q]
    exact quaternion_axis_direction .octahedral 0
  have h3 : Direction f (complexMatrix (q 3)) := by
    rw [direction_iff_source_pull,←complexMatrix_pull,Coordinates.Models.z_raw,
      complexMatrix_ms]
    exact (source_group_iff_standard _).mpr
      ⟨embed (Coordinates.Models.zScale f),
        embed_ne_zero (Coordinates.Models.zScale_nonzero f),Coordinates.Models.zIndex f,rfl⟩
  have h1 : Direction f (Matrix.of (quaternionBasis 1)) := by
    have he : Matrix.of (quaternionBasis 1) =
        Complex.I • (Holant.Certificates.MatchingContractionClosure.X : BinaryMatrix) := by
      ext a b
      cases a <;> cases b <;>
        simp [quaternionBasis,Q1,Holant.Certificates.MatchingContractionClosure.X,
          Signature.disequality]
    rw [he]
    exact (direction_X f).smul Complex.I_ne_zero
  have h2 : Direction f (Matrix.of (quaternionBasis 2)) := by
    have he : Matrix.of (quaternionBasis 1)*Matrix.of (quaternionBasis 3) =
        Matrix.of (quaternionBasis 2) := by
      ext a b
      cases a <;> cases b <;>
        simp [Matrix.mul_apply,quaternionBasis,Q1,Q2,Q3,Complex.I_sq]
    rw [←he]
    exact direction_mul h1 (by simpa [complexMatrix_q,quaternionBasis] using h3)
  fin_cases i
  · simpa [complexMatrix_q,quaternionBasis] using h0
  · exact h1
  · exact h2
  · simpa [complexMatrix_q,quaternionBasis] using h3

theorem roots_axis (f : Form) (i : Fin 4) : Pi.single i 1 ∈ Roots f := by
  rw [←coordinates_basis]
  exact ⟨_,direction_quaternion f i,rfl⟩

theorem roots_detects (f : Form) : Detects (Roots f) := by
  intro v hv
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  refine ⟨Pi.single i 1,roots_axis f i,?_⟩
  rw [pairing_axis]
  apply mul_ne_zero _ hi
  intro hz
  have hh := signs_square i
  simp [hz] at hh

/-- Complete arbitrary-matrix rank-one classification in the actual f
root set, obtained from its produced saturation and spanning axes. -/
theorem rank_one_preserver_iff (f : Form) (A : End) (hr : A.rank = 1) :
    TwoSided (Roots f) A ↔
      ∃ u v : V, u ∈ Roots f ∧ v ∈ Roots f ∧ A = outer u v :=
  rank_one_twoSided_iff (roots_saturated f) (roots_detects f) A hr

theorem typed_rank_one_reconstruction (f : Form) (A : End) (hr : A.rank = 1)
    (h : TwoSided (Roots f) A) :
    ∃ U W : BinaryMatrix, Direction f U ∧ Direction f W ∧
      U.det ≠ 0 ∧ W.det ≠ 0 ∧ reconstruct A = (2 : ℂ)⁻¹ • P0 U W := by
  obtain ⟨u,v,hu,hv,rfl⟩ := (rank_one_preserver_iff f A hr).mp h
  have hU : Direction f (assemble v) := (mem_coefficientSet_iff _ v).mp hv
  have hW : Direction f (assemble u) := (mem_coefficientSet_iff _ u).mp hu
  exact ⟨assemble v,assemble u,hU,hW,hU.det_ne_zero,hW.det_ne_zero,reconstruct_outer u v⟩

theorem rightX_det_ne_zero : Matrix.det rightX ≠ 0 := by
  have hh := congrArg Matrix.det rightX_square
  simp only [Matrix.det_mul,Matrix.det_one] at hh
  intro hz
  simp only [hz,zero_mul] at hh
  exact zero_ne_one hh

theorem transfer_rank (q : FourTensor) (e : PortOrder) :
    (transferMatrix q e).rank = (cardMatrix (relabel e q)).rank :=
  Matrix.rank_mul_eq_right_of_det_ne_zero _ _ rightX_det_ne_zero

theorem cardMatrix_zero : cardMatrix (0 : FourTensor) = 0 := by
  ext i j
  fin_cases i <;> simp [cardMatrix,coordinates_apply,quaternionCoefficient]

theorem reconstruct_zero : reconstruct (0 : End) = 0 := by
  ext x
  simp [reconstruct,assemble]

theorem card_rank_zero_iff (q : FourTensor) : (cardMatrix q).rank = 0 ↔ q = 0 := by
  rw [TetrahedralPreservers.rank_zero_iff]
  constructor
  · intro h
    have hh := reconstruct_cardMatrix q
    rw [h,reconstruct_zero] at hh
    exact hh.symm
  · rintro rfl
    exact cardMatrix_zero

/-- The genuine 2|2 partition is reconstructed from an arbitrary rank-one
map, with nonzero factors. It does not install either factor as a gadget. -/
theorem card_rank_one_factor (q : FourTensor) (hr : (cardMatrix q).rank = 1) :
    HasProperTensorFactor q := by
  obtain ⟨U,W,hU,hW,he⟩ := rank_one_reconstruction (cardMatrix q) hr
  have hq : q = (2 : ℂ)⁻¹ • P0 U W := by
    simpa only [reconstruct_cardMatrix] using he
  have hu : binarySignature U ≠ (0 : Signature ℂ 2) := by
    intro hz
    apply hU
    ext a b
    change _ = (0 : ℂ)
    have hh := congrFun hz ![a,b]
    simpa only [binarySignature,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] using hh
  have hw : binarySignature W ≠ (0 : Signature ℂ 2) := by
    intro hz
    apply hW
    ext a b
    change _ = (0 : ℂ)
    have hh := congrFun hz ![a,b]
    simpa only [binarySignature,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.zero_apply] using hh
  refine ⟨2,2,by decide,by decide,
    finSumFinEquiv.trans
      (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralClassifier.matchingFrame 0),
    (2 : ℂ)⁻¹ • binarySignature U,binarySignature W,
    smul_ne_zero (by norm_num) hu,hw,?_⟩
  rw [hq]
  change (2 : ℂ)⁻¹ • matchingProduct 0 U W = _
  rw [Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralCurrent.matching_tensor]
  ext x
  simp [Tensor.reindex,Tensor.tensor,mul_assoc]

theorem relabel_ne_zero (q : FourTensor) (hq : q ≠ 0) (e : PortOrder) :
    relabel e q ≠ 0 := by
  intro hz
  apply hq
  have hh : Tensor.reindex e (relabel e q) = 0 := by rw [hz]; rfl
  simpa only [Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralLiteralDeck.relabel,
    Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl] using hh

/-- Neither rank zero nor rank one can occur at a nonzero tensor-prime
saved q4. No assertion excluding rank three or classifying rank two/four
is silently imported from the tetrahedral certificate. -/
theorem prime_possible_ranks (q : FourTensor) (hn : q ≠ 0)
    (hp : ¬HasProperTensorFactor q) (e : PortOrder) :
    (transferMatrix q e).rank = 2 ∨ (transferMatrix q e).rank = 3 ∨
      (transferMatrix q e).rank = 4 := by
  rw [transfer_rank]
  have hzero : (cardMatrix (relabel e q)).rank ≠ 0 := by
    intro hr
    exact relabel_ne_zero q hn e ((card_rank_zero_iff _).mp hr)
  have hone : (cardMatrix (relabel e q)).rank ≠ 1 := by
    intro hr
    exact hp ((factor_reindex_iff e.symm q).mp (card_rank_one_factor _ hr))
  have hle : (cardMatrix (relabel e q)).rank ≤ 4 := Matrix.rank_le_width _
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
