import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinRMPhaseProgram

/-! Arbitrary coefficient phase tables on literal RM8 support and the exact
four-entry polynomial values of the seven physical phase probes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseSource
open Holant
namespace R
export GlobalCloseCompletionKleinH6RMBell (rmCheck)
end R
namespace T
export GlobalCloseCompletionKleinRMPhaseTable (positions)
end T
namespace N
export GlobalCloseCompletionKleinGramNorm (wordIndex)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def index4 (x : Fin 4→Bool) : Fin 16 := finProdFinEquiv
  (N.wordIndex (fun i=>x (Fin.castAdd 2 i)),N.wordIndex (fun i=>x (Fin.natAdd 2 i)))
def codeIndex (x : Fin 8→Bool) : Fin 16 := index4 ![x 0,x 1,x 2,x 4]

variable {K : Type*} [CommRing K]

def source (v : Fin 16→K) : Signature K 8 := fun x=>if R.rmCheck x then v (codeIndex x) else 0

def values (v : Fin 16→K) (j : Fin 7) : Fin 4→K :=
  ![![(v 0*v 0) + (v 3*v 9),(v 5*v 14) + (v 6*v 7),(v 9*v 8) + (v 10*v 1),(v 12*v 6) + (v 15*v 15)],
    ![(v 0*v 11) + -(v 8*v 3),-(v 6*v 15) + (v 14*v 7),-(v 1*v 8) + (v 9*v 0),(v 7*v 12) + -(v 15*v 4)],
    ![(v 2*v 3),(v 5*v 4),-(v 10*v 11),-(v 13*v 12)],
    ![(v 0*v 8) + (v 13*v 10),-(v 6*v 0) + -(v 11*v 2),(v 4*v 13) + (v 9*v 15),-(v 2*v 5) + -(v 15*v 7)],
    ![-(v 2*v 12),(v 3*v 14),-(v 12*v 1),(v 13*v 3)],
    ![(v 0*v 13) + -(v 13*v 1),-(v 12*v 8) + (v 1*v 4),(v 14*v 11) + -(v 3*v 7),-(v 2*v 14) + (v 15*v 2)],
    ![(v 14*v 7) + -(v 10*v 3),(v 7*v 2) + -(v 3*v 6),-(v 12*v 9) + (v 8*v 13),-(v 5*v 12) + (v 1*v 8)]] j

def table (v : Fin 16→K) (j : Fin 7) : Signature K 4 := fun x=>
  ∑k : Fin 4,if index4 x=T.positions j k then values v j k else 0

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinRMPhaseSource
end
