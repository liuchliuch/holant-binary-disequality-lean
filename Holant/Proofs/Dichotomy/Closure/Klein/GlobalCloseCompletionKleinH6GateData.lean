import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixFiniteForms

/-! Exact three-versus-three H6 matrix and its transpose inverse, checked
in integers before transport to an arbitrary original coefficient field. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateData
open Holant
namespace H
export GlobalCloseCompletionKleinSixFiniteForms (coreInteger core_cast)
end H
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
abbrev Word3 := Fin 3→Bool

def join (x y : Word3) : Fin 6→Bool := ![x 0,x 1,x 2,y 0,y 1,y 2]
def matrix (transpose : Bool) (x y : Word3) : ℤ :=
  if transpose then H.coreInteger (join y x) else H.coreInteger (join x y)

theorem inverse : ∀(b : Bool) (x y : Word3),
    (∑u : Word3,matrix (!b) x u*matrix b u y)=if x=y then 4 else 0 := by decide +kernel

theorem matrix_cast {K : Type*} [Field K] (b : Bool) (x y : Word3) :
    (matrix b x y:K)=if b then GlobalCloseCompletionKleinH6RMBell.core (join y x)
      else GlobalCloseCompletionKleinH6RMBell.core (join x y) := by
  cases b <;> simp only [matrix,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,H.core_cast]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinH6GateData
