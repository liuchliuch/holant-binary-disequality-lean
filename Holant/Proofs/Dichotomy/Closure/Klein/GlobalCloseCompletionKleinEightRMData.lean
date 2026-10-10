import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinGramCertificate

/-! Literal RM8 chart of an equally weighted translated four-Bell fiber.
Only native bit translations, one pair reversal and two linear signs occur. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMData
open Holant
namespace C
export GlobalCloseCompletionKleinGramCertificate (pauli)
end C
namespace R
export GlobalCloseCompletionKleinH6RMBell (rmCheck)
end R
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def sign (b : Bool) : ℤ := if b then -1 else 1
def weight (s : Fin 8) (k : Fin 4) : ℤ := if k=0 then 1 else sign (s.val.testBit (k.val-1))
def shift (b : Fin 8) (e : Fin 4) : Bool := if e=0 then false else b.val.testBit (e.val-1)
def toggle (k : Fin 4) : Fin 4 := ![1,0,3,2] k

def source (s b : Fin 8) (x : Fin 8→Bool) : ℤ := ∑k : Fin 4,weight s k*
  ∏e : Fin 4,C.pauli (if shift b e then toggle k else k)
    (x (finProdFinEquiv (e,(0:Fin 2)))) (x (finProdFinEquiv (e,(1:Fin 2))))

def reverse (s : Fin 8) : Bool := (s.val.testBit 0 ^^ s.val.testBit 1) ^^ s.val.testBit 2
noncomputable def order (s : Fin 8) : Equiv.Perm (Fin 8) :=
  if reverse s then Equiv.swap 0 1 else Equiv.refl _
def mask (s b : Fin 8) : Fin 8→Bool :=
  ![s.val.testBit 1,s.val.testBit 1,false,b.val.testBit 0,false,b.val.testBit 1,false,b.val.testBit 2]
noncomputable def word (s b : Fin 8) (x : Fin 8→Bool) : Fin 8→Bool := fun i=>x (order s i) ^^ mask s b (order s i)

def correction (s : Fin 8) (x : Fin 8→Bool) : ℤ := sign (s.val.testBit 0 && (x 0 ^^ x 1))
def rm (x : Fin 8→Bool) : ℤ := if R.rmCheck x then 1 else 0
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMData
