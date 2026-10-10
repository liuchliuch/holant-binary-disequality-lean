import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node039
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node048

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node049Rows : List Row := [[(0,(1)),(3,(1))],[(5,(1)),(6,(1))]]
def node049Reduction : Bool→Reduction := fun t=>if t then { rows := node048Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node039Rows, witnesses := fun i => ([{ denominator := 1, weights := [(1,(-1)),(2,(1))] },{ denominator := 1, weights := [(0,(1)),(1,(1)),(2,(-1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node049Covers : Covers node049Rows := by
  apply covers_split _ 2 node049Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node039Covers
    · exact node048Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
