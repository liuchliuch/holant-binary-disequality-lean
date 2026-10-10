import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffinePorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionCore

/-! Complete finite pin/contraction plans for every non-dual seven-port
simplex coset. Normalization changes only the description of the same
support; each plan uses literal pins and one ordinary equal-pair trace. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSevenShiftPlan
open Holant Holant.Tractable Holant.Tractable.AffinePhase
namespace C
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
export NoXReciprocalMixedProjectionCore (logical)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false

def parity (x : Word 7) : Bool:=(((((x 0^^x 1)^^x 2)^^x 3)^^x 4)^^x 5)^^x 6
def NonDual (sign : Word 7) : Prop:=∃x : Word 3,parity (fun j=>sign j && C.codeSeven x j)=true
instance (sign : Word 7) : Decidable (NonDual sign):=inferInstanceAs (Decidable (∃x : Word 3,parity (fun j=>sign j && C.codeSeven x j)=true))

def syndrome (sign : Word 7) : Word 4:=
  ![sign 3^^(sign 1^^sign 2),sign 4^^(sign 0^^sign 2),sign 5^^(sign 0^^sign 1),
    sign 6^^((sign 0^^sign 1)^^sign 2)]
def classIndex (sign : Word 7) : Fin 16:=
  (if syndrome sign 0 then 1 else 0)+(if syndrome sign 1 then 2 else 0)+
    (if syndrome sign 2 then 4 else 0)+(if syndrome sign 3 then 8 else 0)
def representative (c : Fin 16) : Word 7:=
  ![false,false,false,Nat.testBit c.val 0,Nat.testBit c.val 1,Nat.testBit c.val 2,Nat.testBit c.val 3]

theorem class_repr (sign : Word 7) : representative (classIndex sign)=
    C.logical sign (C.codeSeven ![sign 0,sign 1,sign 2]):=by
  revert sign
  decide

theorem nonDual_iff_index (sign : Word 7) : NonDual sign ↔ classIndex sign≠0 ∧ classIndex sign≠7:=by
  revert sign
  decide

theorem same_support (sign z : Word 7) :
    (∃x : Word 3,C.logical sign z=C.codeSeven x) ↔
      (∃x : Word 3,C.logical (representative (classIndex sign)) z=C.codeSeven x):=by
  rw [class_repr]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨xor ![sign 0,sign 1,sign 2] x,?_⟩
    funext j
    rw [NoXReciprocalRankThreeAffinePorts.code_add]
    have h:=congrFun hx j
    change ((sign j^^C.codeSeven ![sign 0,sign 1,sign 2] j)^^z j)=_
    rw [←h]
    simp only [C.logical]
    cases sign j <;> cases C.codeSeven ![sign 0,sign 1,sign 2] j <;> cases z j <;> rfl
  · rintro ⟨x,hx⟩
    refine ⟨xor ![sign 0,sign 1,sign 2] x,?_⟩
    funext j
    rw [NoXReciprocalRankThreeAffinePorts.code_add]
    have h:=congrFun hx j
    change (sign j^^z j)=_
    rw [←h]
    change (sign j^^z j)=(C.codeSeven ![sign 0,sign 1,sign 2] j^^((sign j^^C.codeSeven ![sign 0,sign 1,sign 2] j)^^z j))
    cases sign j <;> cases C.codeSeven ![sign 0,sign 1,sign 2] j <;> cases z j <;> rfl

def orderTable : Fin 16→Fin 7→Fin 7:=
  ![![0,1,2,3,4,5,6],
    ![0,2,4,1,5,6,3],
    ![1,2,3,0,5,6,4],
    ![1,2,3,0,5,6,4],
    ![1,2,3,0,4,6,5],
    ![1,2,3,0,4,6,5],
    ![0,2,4,1,3,6,5],
    ![0,1,2,3,4,5,6],
    ![1,2,3,0,4,5,6],
    ![1,2,3,0,4,5,6],
    ![0,2,4,1,3,5,6],
    ![0,1,5,3,4,6,2],
    ![0,1,5,2,3,4,6],
    ![0,2,4,3,5,6,1],
    ![1,2,3,4,5,6,0],
    ![1,2,3,4,5,6,0]]
def inverseTable : Fin 16→Fin 7→Fin 7:=
  ![![0,1,2,3,4,5,6],
    ![0,3,1,6,2,4,5],
    ![3,0,1,2,6,4,5],
    ![3,0,1,2,6,4,5],
    ![3,0,1,2,4,6,5],
    ![3,0,1,2,4,6,5],
    ![0,3,1,4,2,6,5],
    ![0,1,2,3,4,5,6],
    ![3,0,1,2,4,5,6],
    ![3,0,1,2,4,5,6],
    ![0,3,1,4,2,5,6],
    ![0,1,6,3,4,2,5],
    ![0,1,3,4,5,2,6],
    ![0,6,1,3,2,4,5],
    ![6,0,1,2,3,4,5],
    ![6,0,1,2,3,4,5]]
def order (c : Fin 16) : Equiv.Perm (Fin 7) where
  toFun:=orderTable c
  invFun:=inverseTable c
  left_inv:=by revert c;decide
  right_inv:=by revert c;decide

def pin (c : Fin 16) (i : Fin 3) : Bool:=representative c (order c (Fin.castLE (by decide : 3≤7) i))
def input (c : Fin 16) (t : Bool) (x : Word 2) : Word 7:=
  ![pin c 0,pin c 1,pin c 2,t,t,x 0,x 1]
def wire (c : Fin 16) (t : Bool) (x : Word 2) : Word 7:=
  fun j=>input c t x ((order c).symm j)

theorem support (c : Fin 16) (h0 : c≠0) (h7 : c≠7) (t : Bool) (x : Word 2) :
    (∃u : Word 3,C.logical (representative c) (wire c t x)=C.codeSeven u) ↔
      x 0≠x 1 ∧ t=x 0:=by
  revert c t x
  decide


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSevenShiftPlan
