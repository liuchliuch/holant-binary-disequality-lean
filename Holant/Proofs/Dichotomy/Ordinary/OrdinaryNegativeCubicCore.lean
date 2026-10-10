import Holant.Signature

/-! The ternary cubic sign, over any coefficient type with one and negation. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicCore
open Holant

def cubic {K : Type*} [Neg K] [One K] : Signature K 3 :=
  fun x => if x 0 && x 1 && x 2 then -1 else 1

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeCubicCore
