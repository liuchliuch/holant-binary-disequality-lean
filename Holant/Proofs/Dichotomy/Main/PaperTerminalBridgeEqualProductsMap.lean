import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeEqualProductsAlgebra
import Holant.Proofs.Algorithms.RingHomRealization

/-! The two-copy equal-product programme commutes with the original field
embedding. All native coefficients and all actual vertex labels are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMap
open Holant Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace RH
export RingHomRealization (mapSignature mapFamily)
end RH
namespace T
export EightVertexGaugeTwoRowNetwork (onPorts onPorts_denote denote term)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K L : Type} [Field K] [Field L]

theorem dense_iff (phi : K→+*L) (q : Signature K 4) :
    StableDenseParityAlgebra.Dense (RH.mapSignature phi q) ↔ StableDenseParityAlgebra.Dense q := by
  simp only [StableDenseParityAlgebra.Dense,entries,RH.mapSignature,map_ne_zero]

theorem products_iff (phi : K→+*L) (q : Signature K 4) :
    StableDenseResidualGaugeCore.Products (RH.mapSignature phi q) ↔ StableDenseResidualGaugeCore.Products q := by
  simp only [StableDenseResidualGaugeCore.Products,entries,RH.mapSignature,←map_mul,phi.injective.eq_iff]

theorem even_iff (phi : K→+*L) (q : Signature K 4) :
    EvenSupport (RH.mapSignature phi q) ↔ EvenSupport q := by
  simp only [EvenSupport,RH.mapSignature,map_eq_zero]

theorem programme (phi : K→+*L) (q : Signature K 4) (e : Equiv.Perm (Fin 4)) (cross : Bool) :
    RH.mapSignature phi (T.onPorts q q e e cross).denote=
      (T.onPorts (RH.mapSignature phi q) (RH.mapSignature phi q) e e cross).denote := by
  funext x
  change phi ((T.onPorts q q e e cross).denote x)=_
  rw [T.onPorts_denote,T.onPorts_denote,T.denote,T.denote]
  simp only [T.term,RH.mapSignature,Tensor.reindex,map_add,map_mul]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsMap
end
