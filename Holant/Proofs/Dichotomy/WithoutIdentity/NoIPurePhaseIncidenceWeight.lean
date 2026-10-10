import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRecipeFactor

/-! The modulo-four kernel is derived from the weights of actual original-port
support words. Constants and negative character incidences remain explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceWeight
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word)
open scoped BigOperators
namespace W
export NoIPurePhaseRecipeFactor (incidence)
end W
namespace C
export NoIPurePhaseIncidenceCore (bit evenBit rank_two rank_three)
end C
namespace A
export NoIPurePhaseIncidenceCore.C (codeThree codeSeven)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false

variable {n m : ℕ}

theorem weight_difference (p : Fin n→Port m) (z : Fin m→Bool) :
    (weight (word p z) : ℤ)-weight (word p (fun _=>false))=
      ∑j,W.incidence p j*(if z j then 1 else 0) := NoIPurePhaseRecipeFactor.weight_difference p z

def residue (p : Fin n→Port m) (j : Fin m) : ZMod 4:=W.incidence p j

theorem weight_difference_mod (p : Fin n→Port m) (z : Fin m→Bool) :
    (weight (word p z) : ZMod 4)-weight (word p (fun _=>false))=
      ∑j,residue p j*C.bit (z j) := by
  have h:=congrArg (fun x : ℤ=>(x : ZMod 4)) (weight_difference p z)
  simpa [residue,C.bit,Int.cast_sub,Int.cast_sum,Int.cast_mul] using h

theorem sum_zero (p : Fin n→Port m) (z : Fin m→Bool)
    (same : weight (word p z)%4=weight (word p (fun _=>false))%4) :
    ∑j,residue p j*C.bit (z j)=0 := by
  rw [←weight_difference_mod]
  apply sub_eq_zero.mpr
  exact (ZMod.natCast_eq_natCast_iff' _ _ 4).mpr same


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidenceWeight
end
