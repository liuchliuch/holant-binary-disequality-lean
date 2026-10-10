import Holant.Proofs.Hardness.GeneralEOOriginalCapGraph

/-! Swap only the ordered boundary ports of the actual original-row cap.
The original vertex and every native-X loop are retained verbatim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapOrientation
open Holant Holant.Complexity
namespace N
export GeneralEOOriginalCapGraph (graph assignment denote_coefficients)
end N
variable {n r : ℕ}

def swapped (e : Fin n ≃ (Fin 2 ⊕ (Fin r×Bool))) :
    Fin n ≃ (Fin 2 ⊕ (Fin r×Bool)) :=
  e.trans (Equiv.sumCongr (Equiv.swap 0 1) (Equiv.refl _))

theorem assignment_swapped (e : Fin n ≃ (Fin 2 ⊕ (Fin r×Bool)))
    (x : Fin 2→Bool) (z : (Fin r×Bool)→Bool) :
    N.assignment (swapped e) x z=N.assignment e (fun i=>x (Equiv.swap 0 1 i)) z := by
  funext i
  unfold N.assignment swapped
  simp only [Equiv.trans_apply,Equiv.sumCongr_apply]
  cases e i <;> rfl

variable {K : Type*} [CommSemiring K]

theorem denote_swapped (e : Fin n ≃ (Fin 2 ⊕ (Fin r×Bool)))
    (f : Signature K n) (x : Fin 2→Bool) :
    (N.graph (swapped e) f).denote x=(N.graph e f).denote (fun i=>x (Equiv.swap 0 1 i)) := by
  simp only [N.denote_coefficients,assignment_swapped]

theorem first_swapped (e : Fin n ≃ (Fin 2 ⊕ (Fin r×Bool))) (f : Signature K n) :
    (N.graph (swapped e) f).denote ![false,true]=(N.graph e f).denote ![true,false] := by
  rw [denote_swapped]
  congr 1
  decide

theorem second_swapped (e : Fin n ≃ (Fin 2 ⊕ (Fin r×Bool))) (f : Signature K n) :
    (N.graph (swapped e) f).denote ![true,false]=(N.graph e f).denote ![false,true] := by
  rw [denote_swapped]
  congr 1
  decide

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapOrientation
