import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMActual
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardNamedCore
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinNonrealDescent

/-! Recover the H6 source multiplier from an actual original coefficient,
then apply the checked four-copy circuit over that same original field.
A complex normal-form equality does not grant an unlicensed normalized row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMOriginal
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export GlobalCloseCompletionKleinH6RMBell (core E bell theta core_algebraic)
end B
namespace A
export GlobalCloseCompletionKleinH6RMActual (rm_actual)
end A
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type*} [Field K] [Field L]

theorem map_core_apply (phi : K→+*L) (x : Fin 6→Bool) : phi (B.core (K:=K) x)=B.core (K:=L) x := by
  have factor (k : Fin 4) (u v : Bool) : phi (B.E (K:=K) k u v)=B.E (K:=L) k u v := by
    fin_cases k <;> cases u <;> cases v <;> simp [B.E,B.bell]
  simp only [B.core,map_sum,map_mul,factor]

theorem core_zero : B.core (K:=K) (fun _=>false)=1 := by
  norm_num [B.core,Fin.sum_univ_succ,B.E,B.bell,B.theta]

theorem core_complex : B.core (K:=ℂ)=Holant.ReedMuller.CharacterFlat.hCore := by
  have h : (fun x=>CyclicBoundary.AlgebraicRepresentatives.inclusion (B.core (K:=AlgebraicComplex) x))=
      B.core (K:=ℂ) := funext (map_core_apply _)
  rw [B.core_algebraic] at h
  exact h.symm.trans GlobalCloseCompletionKleinStandardNamedCore.core_complex

theorem recover_scale (phi : K→+*L) (f : Signature K 6) (c : L) (nonzero : c≠0)
    (equation : RingHomRealization.mapSignature phi f=c • B.core) :
    ∃d : K,d≠0 ∧ f=d • B.core := by
  have first := congrFun equation (fun _=>false)
  change phi (f (fun _=>false))=c*B.core (fun _=>false) at first
  rw [core_zero,mul_one] at first
  refine ⟨f (fun _=>false),?_,?_⟩
  · intro zero
    apply nonzero
    rw [←first,zero,map_zero]
  · funext x
    apply phi.injective
    change phi (f x)=phi (f (fun _=>false)*B.core x)
    rw [map_mul,map_core_apply,first]
    exact congrFun equation x

variable [CharZero K]

theorem rm_from_mapped (F : SignatureFamily K) (identity : RetainsIdentity F)
    (phi : K→+*L) (f : Signature K 6) (actual : Gadget.Realizes F .disequality f)
    (c : L) (nonzero : c≠0) (equation : RingHomRealization.mapSignature phi f=c • B.core) :
    ∃d : K,d≠0 ∧ Gadget.Realizes F .disequality (d • R.rm) := by
  obtain ⟨d,hd,hf⟩ := recover_scale phi f c nonzero equation
  rw [hf] at actual
  exact A.rm_actual F identity d hd actual

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

theorem current_actual (f : Signature (OI.K G) 6)
    (actual : Gadget.Realizes P.family .disequality f) (c : ℂ) (nonzero : c≠0)
    (equation : RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G) f=
      c • Holant.ReedMuller.CharacterFlat.hCore) :
    ∃d : OI.K G,d≠0 ∧ Gadget.Realizes P.family .disequality (d • R.rm) := by
  apply rm_from_mapped P.family P.equality (ClosurePhysicalBridge.complexEmbedding G) f actual c nonzero
  rwa [core_complex]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6RMOriginal
end
