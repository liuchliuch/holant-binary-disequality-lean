import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node034
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node049

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node050Rows : List Row := [[(0,(1)),(3,(1))]]
def node050Reduction : Bool→Reduction := fun t=>if t then { rows := node049Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node034Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node050Covers : Covers node050Rows := by
  apply covers_split _ 1 node050Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node034Covers
    · exact node049Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
