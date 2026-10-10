import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryIsotropicSource

/-! A zero own-axis endpoint is an exact nonzero tensor power of the
perpendicular unary in the original coefficient field. The latter is proved
independent of the actual starting unary. This is algebraic factor data for
the genuine power-extraction source, not an assumed unary graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroPower
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace U
export GeneralOddNonisotropicFrame (norm chart inverse frame inverse_frame)
end U
namespace D
export GlobalCloseCompletionUnaryIsotropicSource (determinant)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def opposite (u : Signature K 1) : Bool→K := fun b=>U.inverse u b true

theorem independent (u : Signature K 1) (hu : U.norm u≠0) :
    D.determinant u (fun x=>opposite u (x 0))=1 := by
  have h : D.determinant u (fun x=>opposite u (x 0))=(U.norm u)⁻¹*U.norm u := by
    simp only [D.determinant,opposite,U.inverse,U.frame,U.norm]
    ring
  rw [h,inv_mul_cancel₀ hu]

theorem opposite_nonzero (u : Signature K 1) (hu : U.norm u≠0) : opposite u≠0 := by
  intro zero
  have h := independent u hu
  simp [D.determinant,zero] at h

theorem one_sided (f : Signature K n)
    (support : ∀x,f x≠0→x=(fun _=>false) ∨ x=(fun _=>true))
    (own : f (fun _=>false)=0) : f=purePin (f (fun _=>true)) true n := by
  classical
  funext x
  by_cases ht : x=(fun _=>true)
  · subst x
    simp [purePin]
  have hz : f x=0 := by
    by_contra live
    rcases support x live with hf|ht'
    · exact live (hf ▸ own)
    · exact ht ht'
  simp [purePin,ht,hz]

theorem exact_power (u : Signature K 1) (hu : U.norm u≠0) (f : Signature K n)
    (support : ∀x,U.chart u f x≠0→x=(fun _=>false) ∨ x=(fun _=>true))
    (own : U.chart u f (fun _=>false)=0) :
    f=fun x=>U.chart u f (fun _=>true)*Signature.unaryPower (opposite u) n x := by
  have h := congrArg (Signature.coordinateAction (fun _=>U.inverse u)) (one_sided (U.chart u f) support own)
  simp only [U.chart,Signature.coordinateAction_cancel _ _ (fun _=>U.inverse_frame u hu)] at h
  calc
    f=Signature.coordinateAction (fun _=>U.inverse u)
        (purePin (U.chart u f (fun _=>true)) true n) := h
    _=fun x=>U.chart u f (fun _=>true)*Signature.unaryPower (opposite u) n x := by
      funext x
      simp [Signature.coordinateAction,purePin,Signature.unaryPower,opposite,mul_comm]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroPower
end
