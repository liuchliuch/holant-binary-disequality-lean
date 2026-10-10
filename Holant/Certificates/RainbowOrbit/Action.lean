import Holant.Certificates.MatchingProductBridge.InvertibleBridgeNecessity
import Holant.Certificates.TetrahedralOrientation.Data
import Holant.Certificates.OctahedralSeparator.RankTransport

/-! Literal ordered four-leg actions and the two normalization stages in A.18.
All matrices are ordinary complex matrices; no coefficient similarity is
declared to be a physical generator. -/
namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev BinaryMatrix := Matrix Bool Bool ℂ
abbrev Legs := Fin 4 → BinaryMatrix

def act (L : Legs) (F : FourTensor) : FourTensor := Signature.coordinateAction L F

theorem act_P0 (L : Legs) (U V : BinaryMatrix) :
    act L (P0 U V)=P0 (L 0*U*(L 1).transpose) (L 2*V*(L 3).transpose) := by
  funext x
  simp [act,Signature.coordinateAction,TetrahedralOrientation.sum_four,Fin.prod_univ_succ,
    P0,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  ring

theorem act_P1 (L : Legs) (U V : BinaryMatrix) :
    act L (P1 U V)=P1 (L 0*U*(L 2).transpose) (L 1*V*(L 3).transpose) := by
  funext x
  simp [act,Signature.coordinateAction,TetrahedralOrientation.sum_four,Fin.prod_univ_succ,
    P1,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  ring

theorem act_P2 (L : Legs) (U V : BinaryMatrix) :
    act L (P2 U V)=P2 (L 0*U*(L 3).transpose) (L 1*V*(L 2).transpose) := by
  funext x
  simp [act,Signature.coordinateAction,TetrahedralOrientation.sum_four,Fin.prod_univ_succ,
    P2,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  ring

theorem act_add (L : Legs) (F H : FourTensor) : act L (F+H)=act L F+act L H :=
  Signature.coordinateAction_add _ _ _

theorem act_smul (L : Legs) (c : ℂ) (F : FourTensor) : act L (c • F)=c • act L F := by
  funext x
  simp only [act,Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem act_comp (L M : Legs) (F : FourTensor) : act L (act M F)=act (fun j => L j*M j) F :=
  Signature.coordinateAction_comp _ _ _

theorem act_identity (F : FourTensor) : act (fun _ => (1 : BinaryMatrix)) F=F := by
  change Signature.coordinateAction (fun _ => Signature.equality) F=F
  exact Signature.coordinateAction_equality F

theorem act_inverse (L : Legs) (hL : ∀ j, Matrix.det (L j)≠0) (F : FourTensor) :
    act (fun j => (L j)⁻¹) (act L F)=F := by
  rw [act_comp]
  have hi : (fun j => (L j)⁻¹*L j)=(fun _ => (1 : BinaryMatrix)) := by
    funext j
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hL j))
  rw [hi,act_identity]

theorem act_nonzero (L : Legs) (hL : ∀ j, Matrix.det (L j)≠0) {F : FourTensor} (hF : F≠0) :
    act L F≠0 := by
  intro hz
  apply hF
  have hh := act_inverse L hL F
  rw [hz] at hh
  simpa [act] using hh.symm

theorem act_rescale_legs (L : Legs) (c : Fin 4 → ℂ) (F : FourTensor) :
    act (fun j => c j • L j) F=(∏ j,c j) • act L F := by
  funext x
  simp only [act,Signature.coordinateAction,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,
    Finset.prod_mul_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem A_matrix : A=P0 (1 : BinaryMatrix) (1 : BinaryMatrix) := by
  simp only [A,Q0_matrix]

def firstNormalization (U V : BinaryMatrix) : Legs := ![U⁻¹,1,V⁻¹,1]
def secondNormalization (U : BinaryMatrix) : Legs := ![U⁻¹,U.transpose,1,1]

theorem firstNormalization_A (U V : BinaryMatrix) (hU : U.det≠0) (hV : V.det≠0) :
    act (firstNormalization U V) (P0 U V)=A := by
  rw [act_P0]
  simp [firstNormalization,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hV),A_matrix]

theorem firstNormalization_P1 (U V S T : BinaryMatrix) :
    act (firstNormalization U V) (P1 S T)=P1 (U⁻¹*S*V⁻¹.transpose) T := by
  rw [act_P1]
  simp [firstNormalization]

theorem secondNormalization_A (U : BinaryMatrix) (hU : U.det≠0) :
    act (secondNormalization U) A=A := by
  rw [A_matrix]
  rw [act_P0]
  simp [secondNormalization,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU)]

theorem secondNormalization_P1 (U V : BinaryMatrix) (hU : U.det≠0) :
    act (secondNormalization U) (P1 U V)=P1 (1 : BinaryMatrix) (U.transpose*V) := by
  rw [act_P1]
  simp [secondNormalization,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hU)]

end
end Holant.Certificates.RainbowOrbit
