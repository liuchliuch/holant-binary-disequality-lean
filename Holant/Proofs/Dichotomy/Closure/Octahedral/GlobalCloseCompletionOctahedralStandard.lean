import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTransport
import Holant.Certificates.MatchingProductBridge.GroupInverses

/-! Coefficient extraction from the preserved marked-octahedral proof. Actual standard-O candidate converse. All binary
products, inverses and transposes use the old group-direction producers.
The adjoint below is exactly J_Fr A^T J_Fr, not a Hermitian adjoint.
No candidate legality, normalizer or class-count premise is accepted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.TwoSidedCompleteness
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Preserver
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour
open scoped BigOperators Matrix

theorem theta_zero (U : OctahedralSeparator.Mat) : OctahedralSeparator.theta 0 U = U := by
  change mm (q 0) (mm U (q 0)) = U
  rw [mm_q0,q0_mm]

theorem direction_zero_iff_source (U : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    Direction 0 U ↔ groupDirection .octahedral U := by
  rw [source_group_iff_standard]
  simp only [Direction,theta_zero]

theorem direction_zero_inverse {U : Holant.Certificates.TetrahedralPreservers.BinaryMatrix} (h : Direction 0 U) :
    Direction 0 (@Inv.inv (Matrix Bool Bool ℂ) Matrix.inv U) := by
  apply (direction_zero_iff_source _).mpr
  have hi := groupDirection_inverse .octahedral ((direction_zero_iff_source _).mp h)
  change groupDirection .octahedral (binaryInverse U)
  exact hi

theorem direction_zero_transpose {U : Holant.Certificates.TetrahedralPreservers.BinaryMatrix} (h : Direction 0 U) :
    Direction 0 U.transpose := by
  apply (direction_zero_iff_source _).mpr
  exact groupDirection_transpose .octahedral ((direction_zero_iff_source _).mp h)

theorem direction_zero_one : Direction 0 (1 : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) := by
  have h := Direction.standard 0 0
  simpa only [theta_zero,standard,Matrix.cons_val_zero,complexMatrix_q0] using h

def entryPair (U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) : ℂ := ∑ a : Bool, ∑ b : Bool, U a b*W a b

private theorem assemble_coordinates (U : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    assemble (coordinates U)=U := assemble_coefficient U

private theorem entryPair_sandwich (U W M N : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    entryPair (U*M*W) N = entryPair M (U.transpose*N*W.transpose) := by
  simp [entryPair,Matrix.mul_apply,Matrix.transpose_apply]
  ring

private theorem entryPair_transposeSandwich (U W M N : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    entryPair (U*M.transpose*W) N = entryPair M (W*N.transpose*U) := by
  simp [entryPair,Matrix.mul_apply,Matrix.transpose_apply]
  ring

theorem pairing_entry (r s : V) : entryPair (assemble r) (assemble s) = 2*pairing r s := by
  rw [entryPair,frobenius_pairing]
  change 2*pairing (quaternionCoefficient (assemble r)) (quaternionCoefficient (assemble s)) = _
  rw [coefficient_assemble,coefficient_assemble]

private theorem pairing_swap (u v : V) : pairing u v = pairing v u := by
  unfold pairing
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem pairing_right_ext (u v : V)
    (h : ∀ r : V, pairing r u = pairing r v) : u = v := by
  ext i
  have hi : frobeniusSigns i ≠ 0 := by
    intro hz
    have hs := signs_square i
    rw [hz,zero_mul] at hs
    exact zero_ne_one hs
  have hh := h (Pi.single i 1)
  rw [pairing_swap (Pi.single i 1) u,pairing_swap (Pi.single i 1) v,
    pairing_axis,pairing_axis] at hh
  exact mul_left_cancel₀ hi hh

private theorem sharp_of_pairing (A B : End)
    (h : ∀ r s : V, pairing (A *ᵥ r) s = pairing r (B *ᵥ s)) : sharp A = B := by
  apply matrix_ext_action
  intro s
  apply pairing_right_ext
  intro r
  exact (pairing_adjoint A r s).symm.trans (h r s)

/-- The exact binary-transpose formula for the actual Frobenius sharp. -/
theorem sharp_sandwich (U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    sharp (sandwich U W) = sandwich U.transpose W.transpose := by
  apply sharp_of_pairing
  intro r s
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  rw [←pairing_entry,←pairing_entry,sandwich_action,sandwich_action,
    assemble_coordinates,assemble_coordinates]
  exact entryPair_sandwich U W (assemble r) (assemble s)

/-- Transposition reverses the two factors in the adjoint. There are no
extra factor transposes here: (U M^T W)^* = W M^T U for this bilinear form. -/
theorem sharp_transposeSandwich (U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix) :
    sharp (transposeSandwich U W) = transposeSandwich W U := by
  apply sharp_of_pairing
  intro r s
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  rw [←pairing_entry,←pairing_entry,transposeSandwich_action,transposeSandwich_action,
    assemble_coordinates,assemble_coordinates]
  exact entryPair_transposeSandwich U W (assemble r) (assemble s)

theorem sandwich_safe_zero {U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix} (hU : Direction 0 U) (hW : Direction 0 W) :
    OneSided (Roots 0) (sandwich U W) := by
  intro v hv
  have hK : Direction 0 (assemble v) := (mem_coefficientSet_iff _ v).mp hv
  rw [sandwich_action]
  exact Or.inr ⟨U*assemble v*W,direction_mul (direction_mul hU hK) hW,rfl⟩

theorem transposeSandwich_safe_zero {U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix}
    (hU : Direction 0 U) (hW : Direction 0 W) :
    OneSided (Roots 0) (transposeSandwich U W) := by
  intro v hv
  have hK : Direction 0 (assemble v) := (mem_coefficientSet_iff _ v).mp hv
  rw [transposeSandwich_action]
  exact Or.inr ⟨U*(assemble v).transpose*W,
    direction_mul (direction_mul hU (direction_zero_transpose hK)) hW,rfl⟩

theorem sandwich_twoSided_zero {U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix}
    (hU : Direction 0 U) (hW : Direction 0 W) : TwoSided (Roots 0) (sandwich U W) := by
  refine ⟨sandwich_safe_zero hU hW,?_⟩
  rw [sharp_sandwich]
  exact sandwich_safe_zero (direction_zero_transpose hU) (direction_zero_transpose hW)

theorem kindSandwich_twoSided_zero (b : Bool) {U W : Holant.Certificates.TetrahedralPreservers.BinaryMatrix}
    (hU : Direction 0 U) (hW : Direction 0 W) : TwoSided (Roots 0) (kindSandwich b U W) := by
  cases b
  · exact sandwich_twoSided_zero hU hW
  · refine ⟨transposeSandwich_safe_zero hU hW,?_⟩
    change OneSided (Roots 0) (sharp (transposeSandwich U W))
    rw [sharp_transposeSandwich]
    exact transposeSandwich_safe_zero hW hU

/-- Every returned literal standard candidate satisfies BOTH actual
root conditions. All required inverse/transpose membership is produced. -/
theorem standardCandidate_twoSided (i : ExactAutomorphisms.CandidateIndex) :
    TwoSided (Roots 0) (ExactAutomorphisms.standardCandidate i) := by
  have hleft : Direction 0 (kernel 0 i.1) := Direction.standard 0 i.1
  have hright : Direction 0 (kernel 0 i.2.1) := Direction.standard 0 i.2.1
  exact twoSided_comp (sandwich_twoSided_zero hleft direction_zero_one)
    (kindSandwich_twoSided_zero i.2.2 hright (direction_zero_inverse hright))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankFour.TwoSidedCompleteness
