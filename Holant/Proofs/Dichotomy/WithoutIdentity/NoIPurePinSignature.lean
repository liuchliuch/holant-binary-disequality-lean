import Holant.Algebraic.FixedField
import Holant.Signature
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinProjection
open Holant
variable {K : Type} [Field K]
def pin (bit : Bool) : Signature K 1:=fun x=>if x 0=bit then 1 else 0

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePinProjection
