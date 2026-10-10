import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterResources

/-! All four signed Radon cards are actual outputs in the unchanged original
field/family. Their coefficient embedding is the exact physical network value
up to a retained nonzero substitution multiplier. Character-flatness then
passes through the proved physical/quotient coordinate identity. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterCards
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.CharacterRecognition.SignedTransport
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace A
export GlobalCloseCompletionC2RadonActual (complexEmbedding descend_upTo)
end A
namespace C
export GlobalCloseCompletionKleinCharacterResources (bell complex_resource)
end C
namespace RH
export RingHomRealization (mapSignature mapFamily)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (bells : ∀d l,Gadget.RealizesUpTo F .disequality (C.bell d l))
variable (c : K) (hc : c≠0) (rmActual : Gadget.Realizes F .disequality (c • R.rm))
variable (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)

include bells hc rmActual actual in
theorem actual_cards (v : BinaryVector (n+2)) (hv : Accessible v) :
    ∃frame : RadonFrame (n+2),frame.v=v ∧ ∀d l : ZMod 2,∃q : Signature K n,
      Gadget.Realizes F .disequality q ∧
      (CFlat (RH.mapSignature (A.complexEmbedding phi) q) →
        CFlat (fun x=>actualSignedRadon frame d l
          (fun y=>(RH.mapSignature phi f (wordVector y):ℂ)) (vectorWord x))) := by
  let g := RH.mapSignature (A.complexEmbedding phi) f
  obtain ⟨p,frame,graph,_orthogonal,direction,_adjoint,cards⟩ :=
    SignedRadon.source_accessible_signed_radon (fun _ _=>1) (by intros;exact one_ne_zero) g v hv
  refine ⟨frame,direction,?_⟩
  intro d l
  obtain ⟨uses,native,_equation,_nonzero⟩ := cards d l
  have network := OpenNetworkComposition.realizesUpTo_network (RH.mapFamily (A.complexEmbedding phi) F)
    (SignedRadon.signedNetwork frame graph g d l)
    (fun w=>C.complex_resource phi F bells c hc rmActual f actual _ (uses w)) native (by norm_num)
  obtain ⟨q,s,hs,actualQ,equation⟩ := A.descend_upTo phi F _ network
  refine ⟨q,actualQ,?_⟩
  intro flat
  rw [equation] at flat
  have unscaled := CFlat.smul _ flat s⁻¹
  rw [smul_smul,inv_mul_cancel₀ hs,one_smul] at unscaled
  exact cflat_native_network_implies_actualSignedRadon (by intros;exact one_ne_zero)
    frame graph g d l unscaled

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterCards
end
