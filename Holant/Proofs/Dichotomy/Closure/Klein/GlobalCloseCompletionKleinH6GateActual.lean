import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateCircuit
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6GateAffine

/-! Original-field H6 front-three access. Three actual equality joins retain
the supplied H6 multiplier exactly, and the mapped source is affine precisely
when the mapped result is affine. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateActual
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace A
export GlobalCloseCompletionKleinH6GateAlgebra (action action_scale map_action)
end A
namespace C
export GlobalCloseCompletionKleinH6GateCircuit (circuit actual scale_left core_value)
end C
namespace H
export GlobalCloseCompletionKleinH6RMBell (core)
end H
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type*} [Field K] [Field L] {n : ℕ}

theorem actual (F : SignatureFamily K) (identity : RetainsIdentity F)
    (c : K) (h6 : Gadget.Realizes F .disequality (c • H.core))
    (f : Signature K (n+3)) (actualF : Gadget.Realizes F .disequality f) :
    Gadget.Realizes F .disequality (c • A.action false f) := by
  have h := C.actual F identity (c • H.core) h6 f actualF
  rwa [C.scale_left,C.core_value] at h

theorem mapped (phi : K→+*L) (c : K) (f : Signature K (n+3)) :
    RH.mapSignature phi (c • A.action false f)=(phi c) • A.action false (RH.mapSignature phi f) := by
  funext x
  change phi (c*A.action false f x)=phi c*A.action false (RH.mapSignature phi f) x
  rw [map_mul]
  exact congrArg (fun y=>phi c*y) (congrFun (A.map_action phi false f) x)

theorem scale_affine_iff {m : ℕ} (f : Signature AlgebraicComplex m) (d : AlgebraicComplex) (hd : d≠0) :
    Affine (d • f) ↔ Affine f := by
  constructor
  · intro h
    have hh := h.scale d⁻¹
    convert hh using 1
    funext x
    change f x=d⁻¹*(d*f x)
    rw [←mul_assoc,inv_mul_cancel₀ hd,one_mul]
  · intro h
    exact h.scale d

theorem source (phi : K→+*AlgebraicComplex) (F : SignatureFamily K) (identity : RetainsIdentity F)
    (c : K) (hc : c≠0) (h6 : Gadget.Realizes F .disequality (c • H.core))
    (f : Signature K (n+3)) (actualF : Gadget.Realizes F .disequality f) :
    ∃q : Signature K (n+3),Gadget.Realizes F .disequality q ∧
      RH.mapSignature phi q=(phi c) • A.action false (RH.mapSignature phi f) ∧
      (Affine (RH.mapSignature phi q) ↔ Affine (RH.mapSignature phi f)) := by
  refine ⟨c • A.action false f,actual F identity c h6 f actualF,mapped phi c f,?_⟩
  rw [mapped]
  exact (scale_affine_iff _ _ ((map_ne_zero _).mpr hc)).trans
    (GlobalCloseCompletionKleinH6GateAffine.action_affine_iff false _)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateActual
end
