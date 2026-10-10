import Holant.Tractable.Criteria

namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport
open Holant Holant.Tractable
variable {n : ℕ} (f : Signature AlgebraicComplex n)
def Closed : Prop := ∀a b c,f a≠0 → f b≠0 → f c≠0 → f (tripleXor a b c)≠0
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeClosedSupport
