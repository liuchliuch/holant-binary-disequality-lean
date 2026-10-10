import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureSquareDataCore
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePinSignature

/-! Actual corollas for the retained Eq4 and both pins, with original labels. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareParity
open Holant Holant.Algebraic Holant.Complexity
namespace O
export NativeAntiTargetSource (Output)
end O
set_option backward.isDefEq.respectTransparency false
variable (target : NoIOrdinaryRaw.Target) (D : NoIPureSquareData.Data target)
local instance : Algebra ℚ D.K:=D.K.algebra'
def eq4 : O.Output D.table 4 where
  network:=Network.corolla Holant.EightVertex.ProductAnchor.equalityFour
  labels:={vertex _:=D.eq4
           vertex_arity _:=congrArg Sigma.fst D.eq4_literal
           edge:=Fin.elim0}
  exact:=fun _=>D.eq4_literal
  native:=fun e=>Fin.elim0 e

def pins (b : Bool) : O.Output D.table 1 where
  network:=Network.corolla (Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin b)
  labels:={vertex _:=D.pin b
           vertex_arity _:=congrArg Sigma.fst (D.pin_literal b)
           edge:=Fin.elim0}
  exact:=fun _=>D.pin_literal b
  native:=fun e=>Fin.elim0 e

theorem pins_form (b : Bool) : (pins target D b).network.denote=NoIPurePinProjection.pin b :=
  Network.denote_corolla _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareParity
end
