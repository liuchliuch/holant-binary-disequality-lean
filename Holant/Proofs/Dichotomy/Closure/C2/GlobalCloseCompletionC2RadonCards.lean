import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RadonActual

/-! Flatness of the actual original-field Radon outputs implies the exact
quotient-card hypotheses used by localization and reconstruction. The proved
coordinate isometry and nonzero physical scalar are explicitly removed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RadonCards
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
namespace A
export GlobalCloseCompletionC2RadonActual (complexEmbedding accessible)
end A
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}

theorem quotient_eq_boundary (frame : RadonFrame (n+2)) (ε : ZMod 2) (g : Signature ℂ (n+2)) :
    (fun x=>RadonFrame.actualRadon frame ε (fun y=>g (wordVector y)) (vectorWord x))=
      affineIsometryPullback (RadonFrame.pairToOrdinary frame) 0 (boundaryRadon frame ε g) := by
  funext x
  rw [RadonFrame.actualRadon_eq_quotient]
  simp only [affineIsometryPullback,boundaryRadon,vector_word,sub_zero]
  have coordinates : frame.pairBoundaryLinearEquiv.symm
      ((RadonFrame.pairToOrdinary frame).symm (vectorWord x))=
      frame.ordinaryBoundaryLinearEquiv.symm (vectorWord x) := by
    simp [RadonFrame.pairToOrdinary]
  rw [coordinates]

theorem flat_quotient (frame : RadonFrame (n+2)) (ε : ZMod 2) (g : Signature ℂ (n+2))
    (h : FlatOrZero (boundaryRadon frame ε g)) :
    FlatOrZero (fun x=>RadonFrame.actualRadon frame ε (fun y=>g (wordVector y)) (vectorWord x)) := by
  rw [quotient_eq_boundary]
  exact flatOrZero_affineIsometryPullback _ (RadonFrame.pairToOrdinary_isometry frame) 0 _ h

variable {K : Type*} [Field K] [CharZero K]
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)
variable (c : K) (hc : c≠0) (actualRM : Gadget.Realizes F .disequality (c • R.rm))
variable (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)

include hI hc actualRM actual in
theorem actual_cards (v : BinaryVector (n+2)) (hv : Accessible v) :
    ∃frame : RadonFrame (n+2),frame.v=v ∧ ∀ε : ZMod 2,∃q : Signature K n,
      Gadget.Realizes F .disequality q ∧
      (FlatOrZero (RH.mapSignature (A.complexEmbedding phi) q) →
        FlatOrZero (fun x=>RadonFrame.actualRadon frame ε
          (fun y=>(RH.mapSignature phi f (wordVector y):ℂ)) (vectorWord x))) := by
  obtain ⟨frame,direction,cards⟩ := A.accessible phi F hI c hc actualRM f actual v hv
  refine ⟨frame,direction,?_⟩
  intro ε
  obtain ⟨q,d,hd,actualQ,equation⟩ := cards ε
  refine ⟨q,actualQ,?_⟩
  intro flat
  rw [equation] at flat
  have unscaled := flatOrZero_nonzero_smul _ flat d⁻¹ (inv_ne_zero hd)
  rw [smul_smul,inv_mul_cancel₀ hd,one_smul] at unscaled
  exact flat_quotient frame ε (RH.mapSignature (A.complexEmbedding phi) f) unscaled

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RadonCards
end
