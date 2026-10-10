import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RMContext
import Holant.ReedMuller.TwoChart.FlatLocalizationSource

/-! The actual RM resource transports the phase-free Radon localization back
to a genuine smaller original-field network. Flat lower-card hypotheses stay
explicit; the returned bad tensor is physically available for factor saturation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMLocalization
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching Holant.ReedMuller.TwoChart
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)
variable (c : K) (hc : c≠0) (actualRM : Gadget.Realizes F .disequality (c • R.rm))
variable (f : Signature K n) (actual : Gadget.Realizes F .disequality f)

include hI hc actualRM actual in
theorem from_frame (hn : 10≤n) (even : Even n) (frame : RadonFrame n)
    (cards : ∀d,FlatOrZero (fun x=>RadonFrame.actualRadon frame d
      (fun y=>(RH.mapSignature phi f (wordVector y):ℂ)) (vectorWord x)))
    (bad : ¬Affine (orbitPlus frame.v (RH.mapSignature phi f))) :
    ∃m : ℕ,∃q : Signature K m,m≤8 ∧ 0<m ∧ q≠0 ∧ Gadget.Realizes F .disequality q ∧
      ¬Affine (sourceKBasis.action (RH.mapSignature phi q)) := by
  obtain ⟨m,N,hm,uses,native,_nonzero,nonaffine,_vertices,_edges⟩ :=
    source_flat_two_chart_localization hn even frame (RH.mapSignature phi f) cards bad
  obtain ⟨q,actualQ,badQ,badKQ⟩ := GlobalCloseCompletionC2RMContext.bad_context phi f N
    uses.vertex_mem F hI actual c hc actualRM native nonaffine
  have nonzero : q≠0 := by
    intro h
    apply badQ
    have hz : RH.mapSignature phi q=0 := by funext x; simp [RH.mapSignature,h]
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
  exact ⟨m,q,hm,positive,nonzero,actualQ,badKQ⟩

include hI hc actualRM actual in
theorem from_flat_cards (hn : 10≤n) (even : Even n)
    (cards : FlatRadonCards (fun y=>(RH.mapSignature phi f (wordVector y):ℂ)))
    (bad : ¬Affine (RH.mapSignature phi f)) :
    ∃m : ℕ,∃q : Signature K m,m≤8 ∧ 0<m ∧ q≠0 ∧ Gadget.Realizes F .disequality q ∧
      ¬Affine (sourceKBasis.action (RH.mapSignature phi q)) := by
  have obstruction : ∃v : BinaryVector n,∃hv : Accessible v,¬Affine (orbitPlus v (RH.mapSignature phi f)) := by
    by_contra! h
    exact bad (source_affine_hyperplane_patching hn even _ h)
  obtain ⟨v,hv,hbad⟩ := obstruction
  obtain ⟨frame,direction,hcards⟩ := cards v hv
  apply from_frame phi F hI c hc actualRM f actual hn even frame hcards
  simpa only [direction] using hbad

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMLocalization
end
