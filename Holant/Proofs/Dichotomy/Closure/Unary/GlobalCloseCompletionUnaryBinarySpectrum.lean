import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroPower
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationFamily

/-! The two-sided binary endpoint in a nonisotropic unary chart has literal
orthogonal rank-one spectral projectors in the original coefficient field.
This is the exact positive-chain pencil used to interpolate its perpendicular
unary power, retaining all norm factors and both endpoint coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinarySpectrum
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
open Holant.Certificates.MatchingContractionClosure
namespace U
export GeneralOddNonisotropicFrame (norm chart inverse frame inverse_frame)
end U
namespace Z
export GlobalCloseCompletionUnaryZeroPower (opposite)
end Z
namespace E
export GlobalCloseCompletionUnaryHigherEq4 (endpoint)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K]

def axis (u : Signature K 1) : Bool→K := fun b=>U.inverse u b false
def projector (u : Signature K 1) (p : Bool) : Binary (K:=K) :=
  fun a b=>U.norm u*U.inverse u a p*U.inverse u b p

theorem projector_mul (u : Signature K 1) (hu : U.norm u≠0) (p q : Bool) :
    projector u p*projector u q=if p=q then projector u p else 0 := by
  ext a b
  cases p <;> cases q <;> cases a <;> cases b <;>
    simp [projector,Matrix.mul_apply,Fintype.sum_bool,U.inverse,U.frame]
  all_goals field_simp [hu]
  all_goals simp only [U.norm] at *
  all_goals ring

theorem projector_sum (u : Signature K 1) (hu : U.norm u≠0) :
    projector u false+projector u true=1 := by
  ext a b
  cases a <;> cases b <;> simp [projector,U.inverse,U.frame,Matrix.one_apply]
  all_goals field_simp [hu]
  all_goals simp only [U.norm] at *
  all_goals ring

theorem endpoint_decomposition {n : ℕ} (u : Signature K 1) (hu : U.norm u≠0)
    (f : Signature K n) (A B : K) (form : U.chart u f=E.endpoint n A B) :
    f=fun x=>A*Signature.unaryPower (axis u) n x+B*Signature.unaryPower (Z.opposite u) n x := by
  have h := congrArg (Signature.coordinateAction (fun _=>U.inverse u)) form
  simp only [U.chart,Signature.coordinateAction_cancel _ _ (fun _=>U.inverse_frame u hu)] at h
  calc
    f=Signature.coordinateAction (fun _=>U.inverse u) (E.endpoint n A B) := h
    _=_ := by
      funext x
      simp [Signature.coordinateAction,E.endpoint,purePin,Signature.unaryPower,axis,Z.opposite,
        mul_add,Finset.sum_add_distrib,mul_comm]

theorem binary_decomposition (u : Signature K 1) (hu : U.norm u≠0)
    (f : Signature K 2) (A B : K) (form : U.chart u f=E.endpoint 2 A B) :
    Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix f=
      (A/U.norm u) • projector u false+(B/U.norm u) • projector u true := by
  ext a b
  rw [Holant.LocalDrafts.FinitePGL2.Stabilization.binaryMatrix,endpoint_decomposition u hu f A B form]
  simp [Signature.unaryPower,Fin.prod_univ_two,axis,Z.opposite,projector]
  field_simp [hu]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBinarySpectrum
end
