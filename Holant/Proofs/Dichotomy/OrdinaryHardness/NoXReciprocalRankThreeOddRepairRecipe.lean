import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeOddRepairCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalResource

/-! The finite repair has two seven-port copies and one actual zero pin.
Three paired negative ports are private; all seven remaining ports occur once. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairRecipe
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace C
export NoXReciprocalRankThreeOddRepairCore (first second exotic correction Exotic sum_value)
export NoXReciprocalMixedProjectionCore (logical)
end C
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false

def arity (i : ℕ) : ℕ := if i=0 then 7 else 1

def rows : Recipe (u:=1) (s:=2) (a:=fun _=>7+3) (b:=arity) := fun _=>
  [⟨0,![.inr (0 : Fin 10),.inr (1 : Fin 10),.inr (2 : Fin 10),.inr (7 : Fin 10),.inr (8 : Fin 10),.inr (9 : Fin 10),.inr (6 : Fin 10)]⟩,
   ⟨0,![.inl false,.inr (4 : Fin 10),.inr (5 : Fin 10),.inr (7 : Fin 10),.inr (9 : Fin 10),.inr (8 : Fin 10),.inr (3 : Fin 10)]⟩,
   ⟨1,fun _=>.inl false⟩]

def resource : D.OddResource (s:=2) arity 7 where
  privateCount := 3
  rows := rows
  constant_even bit := by cases bit <;> decide
  boundary_odd q := by fin_cases q <;> decide
  private_even q := by fin_cases q <;> decide

variable {K : Type} [Field K] (f : Signature K 7)
def table : (i : Fin 2)→Signature K (arity i.val)
  | ⟨0,_⟩=>f
  | ⟨1,_⟩=>OrdinaryNegativeSignedPortsCore.pin false
  | ⟨j+2,h⟩=>False.elim (by omega)

theorem coefficient_value (z : Fin 7→Bool) (t : Fin 3→Bool) :
    coefficient (table f) rows 0 (Fin.addCases z t)=f (C.first z t)*f (C.second z t) := by
  simp [coefficient,Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient,
    rows,table,OrdinaryNegativeSignedPortsCore.pin,C.first,C.second]
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem value (support : ∀z,f z≠0 ↔ C.Exotic z) (z : Fin 7→Bool) :
    OrdinaryNegativeMixedBlockSource.trace (table f) 3 rows 0 z=
      f (C.logical C.exotic z)*f (C.correction z) := by
  unfold OrdinaryNegativeMixedBlockSource.trace
  simp_rw [coefficient_value]
  exact C.sum_value f support z


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairRecipe
end
