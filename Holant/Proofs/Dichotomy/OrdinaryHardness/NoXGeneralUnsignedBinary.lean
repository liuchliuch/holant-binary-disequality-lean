import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenOperations
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Unsigned Boolean minors retain the original row or even resource. A
literal original row is duplicated to give even incidence. A pre-existing
even resource needs no duplication when pinnings/identifications are applied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralUnsignedBinary
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace B
export OrdinaryNegativeSparseMixingSource (Block trace_zero)
end B
namespace O
export NoXGeneralEvenOperations (gadget gadget_value)
end O
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget (direct direct_value)
end G
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
namespace P
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s n m : ℕ} {b : ℕ→ℕ}

variable (row : B.Block (s:=s) (b:=b) n) (q : Fin n→Bool ⊕ Fin m)
def restrict : B.Block (s:=s) (b:=b) m := O.gadget row (G.direct [q])

variable {K : Type} [Field K] (H : (j : Fin s)→Signature K (b j.val))

theorem restrict_value (z : Fin m→Bool) : (restrict row q).signature H z=row.signature H (T.substitute q z) := by
  rw [restrict,O.gadget_value,G.direct_value]
  simp only [P.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]

variable (j : Fin s) (ps : Fin (b j.val)→Bool ⊕ Fin m)
def duplicateRows : Recipe (u:=1) (s:=s) (a:=fun _=>m) (b:=b) := fun _=>[⟨j,ps⟩,⟨j,ps⟩]

theorem duplicate_even : EvenRecipe (duplicateRows j ps) := by
  intro i p
  simp only [ports,duplicateRows,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.count_append]
  exact ⟨_,rfl⟩

def duplicate : B.Block (s:=s) (b:=b) m := ⟨0,duplicateRows j ps,duplicate_even j ps⟩

variable [Algebra ℚ K]
theorem duplicate_value (z : Fin m→Bool) : (duplicate j ps).signature H z=H j (T.substitute ps z)^2 := by
  change OrdinaryNegativeMixedBlockSource.trace H 0 (duplicateRows j ps) 0 z=_
  rw [B.trace_zero]
  change H j (T.substitute ps z)*(H j (T.substitute ps z)*1)=_
  ring

def meet (x y : Fin n→Bool) : Fin n→Bool := fun i=>x i && y i

def join (x y : Fin n→Bool) : Fin n→Bool := fun i=>x i || y i

def pairPorts (x y : Fin n→Bool) : Fin n→Bool ⊕ Fin 2 := fun i=>
  if x i then (if y i then .inl true else .inr 0) else (if y i then .inr 1 else .inl false)

theorem pair_values (x y : Fin n→Bool) :
    T.substitute (pairPorts x y) ![false,false]=meet x y ∧
    T.substitute (pairPorts x y) ![false,true]=y ∧
    T.substitute (pairPorts x y) ![true,false]=x ∧
    T.substitute (pairPorts x y) ![true,true]=join x y := by
  constructor
  · funext i;cases hx : x i <;> cases hy : y i <;> simp [pairPorts,T.substitute,meet,hx,hy]
  constructor
  · funext i;cases hx : x i <;> cases hy : y i <;> simp [pairPorts,T.substitute,hx,hy]
  constructor
  · funext i;cases hx : x i <;> cases hy : y i <;> simp [pairPorts,T.substitute,hx,hy]
  · funext i;cases hx : x i <;> cases hy : y i <;> simp [pairPorts,T.substitute,join,hx,hy]

omit [Algebra ℚ K] in
theorem anti_of_two_zeros (f : Signature K 2) (h0 : f ![false,false]=0) (h1 : f ![true,true]=0) :
    f=NoXWeightedAntiSigned.anti (f ![false,true]) (f ![true,false]) := by
  funext x
  have hx : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> simp only [NoXWeightedAntiSigned.anti]
  · exact h0
  · rfl
  · rfl
  · exact h1


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralUnsignedBinary
end
