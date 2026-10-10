import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node004
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node009

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node010Rows : List Row := [[(0,(1)),(5,(1))],[(1,(1)),(4,(1))],[(2,(1)),(4,(-1))],[(3,(1)),(5,(-1))]]
def node010Reduction : Bool→Reduction := fun t=>if t then { rows := node009Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 2, weights := [(1,(2)),(2,(1)),(4,(-1))] },{ denominator := 2, weights := [(2,(1)),(4,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(2,(-1)),(4,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node004Rows, witnesses := fun i => ([{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(0,(1)),(3,(1)),(4,(-1))] },{ denominator := 1, weights := [(0,(1)),(4,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node010Covers : Covers node010Rows := by
  apply covers_split _ 4 node010Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node004Covers
    · exact node009Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
