import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterResources

/-! Character-aware localization returns an actual smaller nonaffine row over
the original field. Both the context and every Pauli/RM occurrence are realized
from the original family, with their nonzero scalars retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterLocalization
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.CharacterRecognition
open Holant.ReedMuller.CharacterRecognition.SignedTransport
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.TwoChart
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace C
export GlobalCloseCompletionKleinCharacterResources (bell bad_context)
end C
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (bells : ∀d l,Gadget.RealizesUpTo F .disequality (C.bell d l))
variable (c : K) (hc : c≠0) (rmActual : Gadget.Realizes F .disequality (c • R.rm))
variable (f : Signature K n) (actual : Gadget.Realizes F .disequality f)

include bells hc rmActual actual in
theorem from_frame (hn : 10≤n) (even : _root_.Even n) (frame : RadonFrame n)
    (cards : ∀d,CFlat (fun x=>RadonFrame.actualRadon frame d
      (fun y=>(RH.mapSignature phi f (wordVector y):ℂ)) (vectorWord x)))
    (bad : ¬Affine (orbitPlus frame.v (RH.mapSignature phi f))) :
    ∃m : ℕ,∃q : Signature K m,m≤8 ∧ 0<m ∧ q≠0 ∧ Gadget.Realizes F .disequality q ∧
      ¬Affine (RH.mapSignature phi q) := by
  obtain ⟨m,N,hm,uses,native,_nonzero,nonaffine,_vertices,_edges⟩ :=
    source_character_two_chart_localization hn even (fun _ _=>1) (by intros;exact one_ne_zero)
      frame (RH.mapSignature phi f) cards bad
  obtain ⟨q,actualQ,badQ⟩ := C.bad_context phi F bells c hc rmActual f actual N uses.vertex_mem native nonaffine
  have nonzero : q≠0 := by
    intro h
    apply badQ
    have hz : RH.mapSignature phi q=0 := by funext x;simp [RH.mapSignature,h]
    rw [hz]
    exact affine_zero m
  have positive : 0<m := by
    by_contra h
    have hm0 : m=0 := by omega
    subst m
    apply badQ
    have constant : RH.mapSignature phi q=fun _=>phi (q Fin.elim0) := by
      funext x
      exact congrArg (fun y=>phi (q y)) (Subsingleton.elim _ _)
    rw [constant]
    exact affine_constant 0 _
  exact ⟨m,q,hm,positive,nonzero,actualQ,badQ⟩

include bells hc rmActual actual in
theorem from_signed_cards (hn : 10≤n) (even : _root_.Even n)
    (cards : CFlatSignedRadonCards (fun y=>(RH.mapSignature phi f (wordVector y):ℂ)))
    (bad : ¬Affine (RH.mapSignature phi f)) :
    ∃m : ℕ,∃q : Signature K m,m≤8 ∧ 0<m ∧ q≠0 ∧ Gadget.Realizes F .disequality q ∧
      ¬Affine (RH.mapSignature phi q) := by
  have obstruction : ∃v : BinaryVector n,∃hv : Accessible v,¬Affine (orbitPlus v (RH.mapSignature phi f)) := by
    by_contra! h
    exact bad (source_affine_hyperplane_patching hn even _ h)
  obtain ⟨v,hv,hbad⟩ := obstruction
  obtain ⟨frame,direction,hcards⟩ := cards v hv
  apply from_frame phi F bells c hc rmActual f actual hn even frame
  · intro d
    simpa only [actualSignedRadon_plus] using hcards d 0
  · simpa only [direction] using hbad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterLocalization
end
