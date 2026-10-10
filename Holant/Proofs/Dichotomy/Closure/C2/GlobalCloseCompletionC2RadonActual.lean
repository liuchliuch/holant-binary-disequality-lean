import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RMContext
import Holant.ReedMuller.RadonAccess.Source
import Holant.ReedMuller.AffineRadon.PhysicalBridge

/-! Every accessible Radon direction has an actual original-field output,
with its full nonzero substitution multiplier. Literal RM and free scalar
normalization never become assumed resources of the original family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RadonActual
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
namespace RH
export RingHomRealization (mapSignature mapFamily realizes_map realizesUpTo_map)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable (phi : K→+*AlgebraicComplex)
abbrev complexEmbedding : K→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp phi
variable (F : SignatureFamily K) (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)
variable (c : K) (hc : c≠0) (actualRM : Gadget.Realizes F .disequality (c • R.rm))
variable (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)

theorem mapped_rm : RH.mapSignature (complexEmbedding phi) (R.rm (K:=K))=rmCore := by
  funext x
  have h := congrFun (GlobalCloseCompletionC2RMContext.map_rm phi) x
  exact congrArg Subtype.val h

theorem mapped_identity : RH.mapSignature (complexEmbedding phi) (B.identity (K:=K))=
    fun x=>Signature.equality (x 0) (x 1) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [RH.mapSignature,B.identity,Signature.equality,h0,h1]

include hI hc actualRM actual in
theorem resource_actual (q : AnySignature ℂ)
    (member : q∈radonFamily (RH.mapSignature (complexEmbedding phi) f)) :
    Gadget.RealizesUpTo (RH.mapFamily (complexEmbedding phi) F) .disequality q.2 := by
  rcases member with rfl|rfl|rfl|rfl
  · exact ⟨1,one_ne_zero,by simpa using RH.realizes_map (complexEmbedding phi) actual⟩
  · have h := RH.realizes_map (complexEmbedding phi) (Gadget.realizes_of_mem F .disequality B.identity hI)
    rw [mapped_identity] at h
    exact ⟨1,one_ne_zero,by simpa using h⟩
  · exact ⟨1,one_ne_zero,by simpa only [one_mul,EdgeKind.value] using Gadget.realizes_edgeBox (K:=ℂ) (RH.mapFamily (complexEmbedding phi) F) .disequality⟩
  · have h : Gadget.RealizesUpTo F .disequality (R.rm (K:=K)) := ⟨c,hc,actualRM⟩
    have mapped := RH.realizesUpTo_map (complexEmbedding phi) (complexEmbedding phi).injective h
    rwa [mapped_rm] at mapped

theorem descend_upTo {m : ℕ} (g : Signature ℂ m)
    (h : Gadget.RealizesUpTo (RH.mapFamily (complexEmbedding phi) F) .disequality g) :
    ∃q : Signature K m,∃d : ℂ,d≠0 ∧ Gadget.Realizes F .disequality q ∧
      RH.mapSignature (complexEmbedding phi) q=d • g := by
  obtain ⟨d,hd,N,uses,native,equation⟩ := h
  let M := RingHomDescent.descendNetwork (complexEmbedding phi) N uses
  refine ⟨M.tensor,d,hd,⟨M,RingHomDescent.descend_labels (complexEmbedding phi) N uses,native,rfl⟩,?_⟩
  exact (RingHomDescent.descend_tensor (complexEmbedding phi) N uses).trans equation

include hI hc actualRM actual in
theorem accessible (v : BinaryVector (n+2)) (hv : Accessible v) :
    ∃frame : RadonFrame (n+2),frame.v=v ∧ ∀ε : ZMod 2,∃q : Signature K n,∃d : ℂ,
      d≠0 ∧ Gadget.Realizes F .disequality q ∧ RH.mapSignature (complexEmbedding phi) q=
        d • boundaryRadon frame ε (RH.mapSignature (complexEmbedding phi) f) := by
  obtain ⟨p,frame,hA,hv,cards⟩ := source_accessible_radon_native (RH.mapSignature (complexEmbedding phi) f) v hv
  refine ⟨frame,hv,?_⟩
  intro ε
  obtain ⟨N,_literal,uses,native,equation,_vertices,_edges,_actual⟩ := cards ε
  have actualN := OpenNetworkComposition.realizesUpTo_network (RH.mapFamily (complexEmbedding phi) F) N
    (fun w=>resource_actual phi F hI c hc actualRM f actual _ (uses w)) native (by norm_num)
  rw [equation] at actualN
  exact descend_upTo phi F _ actualN

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RadonActual
end
