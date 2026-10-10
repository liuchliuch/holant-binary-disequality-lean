import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMData
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineEightNorm

/-! Exact finite label/bit coordinates of the actual translated Pauli fiber.
The phase part of each shift is a boundary sign; its parity part is the
literal native bit translation used by the RM8 chart. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMLabels
open Holant
namespace H
export GlobalCloseCompletionKleinHigherNonaffine (Label E EOver xLabel yLabel zLabel)
end H
namespace D
export GlobalCloseCompletionKleinEightRMData (sign weight shift toggle)
end D
namespace C
export GlobalCloseCompletionKleinGramCertificate (pauli)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def label : Fin 4→H.Label := ![(0,0),(0,1),(1,0),(1,1)]
def index (a : H.Label) : Fin 4 := ⟨2*a.1.val+a.2.val,by have := a.1.val_lt;have := a.2.val_lt;norm_num at *;omega⟩

theorem index_label : ∀k : Fin 4,index (label k)=k := by decide +kernel
theorem label_index : ∀a : H.Label,label (index a)=a := by decide +kernel

def labelEquiv : Fin 4≃H.Label where
  toFun := label
  invFun := index
  left_inv := index_label
  right_inv := label_index

def pack (v : Fin 3→Bool) : Fin 8 :=
  ⟨(if v 0 then 1 else 0)+2*(if v 1 then 1 else 0)+4*(if v 2 then 1 else 0),by
    cases v 0 <;> cases v 1 <;> cases v 2 <;> decide⟩

theorem pack_bits : ∀v : Fin 3→Bool,∀i : Fin 3,(pack v).val.testBit i.val=v i := by decide +kernel

def phasePack (phase : H.Label→Bool) : Fin 8 := pack ![phase (label 1),phase (label 2),phase (label 3)]
def one (z : ZMod 2) : Bool := decide (z=1)
def shiftPack (shifts : Fin 4→H.Label) : Fin 8 := pack ![one (shifts 1).2,one (shifts 2).2,one (shifts 3).2]

theorem weight_phase : ∀phase : H.Label→Bool,phase 0=false→∀k : Fin 4,
    D.weight (phasePack phase) k=D.sign (phase (label k)) := by decide +kernel

theorem shift_bits : ∀shifts : Fin 4→H.Label,shifts 0=0→∀e : Fin 4,
    D.shift (shiftPack shifts) e=one (shifts e).2 := by decide +kernel

theorem map_E {K L : Type*} [Ring K] [Ring L] (phi : K→+*L) (a : H.Label) (u v : Bool) :
    phi (H.EOver (0:K) a u v)=H.EOver (0:L) a u v := by
  cases u <;> cases v <;> unfold H.EOver
  all_goals split_ifs <;> simp

theorem shifted_E_integer : ∀k : Fin 4,∀a : H.Label,∀u v : Bool,
    H.EOver (0:ℤ) (label k+a) u v=
      D.sign (one a.1 && u)*C.pauli (if one a.2 then D.toggle k else k) u v := by
  decide +kernel

theorem shifted_E {K : Type*} [Field K] (k : Fin 4) (a : H.Label) (u v : Bool) :
    H.EOver (0:K) (label k+a) u v=
      (D.sign (one a.1 && u):K)*(C.pauli (if one a.2 then D.toggle k else k) u v:K) := by
  have h := congrArg (Int.castRingHom K) (shifted_E_integer k a u v)
  rw [map_E,map_mul] at h
  exact h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMLabels
end
