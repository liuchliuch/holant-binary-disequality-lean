import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixMatchingCoordinates
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixCardReal

/-! Literal original-port gauge for any first Bell matching card. Reordering
its two matching edges, translating their second endpoints, and signing their
first endpoints sends the chosen line to I tensor I. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixAnchorData
open Holant
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line)
end D
namespace S
export GlobalCloseCompletionKleinRMPhaseSource (index4)
end S
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def layout (a : Fin 48) : Fin 3 := ⟨a.val/16,by omega⟩
def orderData (a : Fin 48) : Fin 6→Fin 6 :=
  ![![0,1,2,3,4,5],![0,1,2,4,3,5],![0,1,2,4,5,3]] (layout a)
def inverseData (a : Fin 48) : Fin 6→Fin 6 :=
  ![![0,1,2,3,4,5],![0,1,2,4,3,5],![0,1,2,5,3,4]] (layout a)

theorem inverse_left : ∀a i,inverseData a (orderData a i)=i := by decide +kernel
theorem inverse_right : ∀a i,orderData a (inverseData a i)=i := by decide +kernel

def order (a : Fin 48) : Equiv.Perm (Fin 6) where
  toFun := orderData a
  invFun := inverseData a
  left_inv := inverse_left a
  right_inv := inverse_right a

def mask (a : Fin 48) : Fin 6→Bool :=
  ![false,false,false,a.val.testBit 2,false,a.val.testBit 0]
def phaseMask (a : Fin 48) : Fin 6→Bool :=
  ![false,false,a.val.testBit 3,false,a.val.testBit 1,false]
def phaseSet (a : Fin 48) : Finset (Fin 6) := Finset.univ.filter (fun i=>phaseMask a i=true)
def word (a : Fin 48) (x : Fin 6→Bool) : Fin 6→Bool := fun i=>x (order a i) ^^ mask a (order a i)
def weight (a : Fin 48) (x : Fin 6→Bool) : ℤ :=
  (if a.val.testBit 3 && x 2 then -1 else 1)*(if a.val.testBit 1 && x 4 then -1 else 1)
def tailWord (a : Fin 48) (z : Fin 4→Bool) : Fin 4→Bool :=
  fun i=>word a (Fin.addCases (m:=2) (n:=4) (fun _=>false) z) (Fin.natAdd 2 i)

theorem word_pair : ∀a : Fin 48,∀u : Fin 2→Bool,∀z : Fin 4→Bool,
    word a (Fin.addCases (m:=2) (n:=4) u z)=Fin.addCases (m:=2) (n:=4) u (tailWord a z) := by
  decide +kernel

theorem weight_pair : ∀a : Fin 48,∀u : Fin 2→Bool,∀z : Fin 4→Bool,
    weight a (Fin.addCases (m:=2) (n:=4) u z)=
      weight a (Fin.addCases (m:=2) (n:=4) (fun _=>false) z) := by
  decide +kernel

theorem normalized_line : ∀a : Fin 48,∀z : Fin 4→Bool,
    weight a (Fin.addCases (m:=2) (n:=4) (fun _=>false) z)*D.line a (S.index4 (tailWord a z))=
      D.line 0 (S.index4 z) := by
  decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixAnchorData
