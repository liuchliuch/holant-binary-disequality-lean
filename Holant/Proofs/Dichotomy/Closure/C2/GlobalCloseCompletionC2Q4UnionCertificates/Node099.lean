import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node065
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node098

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node099Rows : List Row := [[(4,(1)),(7,(1))]]
def node099Reduction : Bool→Reduction := fun t=>if t then { rows := node098Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node065Rows, witnesses := fun i => ([{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(0,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node099Covers : Covers node099Rows := by
  apply covers_split _ 1 node099Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node065Covers
    · exact node098Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
