import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node011
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node014

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node015Rows : List Row := [[(0,(1)),(6,(-1))],[(1,(1)),(2,(1))],[(3,(1)),(6,(1))],[(5,(1)),(6,(1))]]
def node015Reduction : Bool→Reduction := fun t=>if t then { rows := node014Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1)),(4,(-1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node011Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(1)),(4,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 2, weights := [(0,(1)),(2,(2)),(4,(-1))] },{ denominator := 2, weights := [(0,(1)),(3,(2)),(4,(-1))] },{ denominator := 2, weights := [(0,(-1)),(4,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node015Covers : Covers node015Rows := by
  apply covers_split _ 4 node015Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node011Covers
    · exact node014Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
