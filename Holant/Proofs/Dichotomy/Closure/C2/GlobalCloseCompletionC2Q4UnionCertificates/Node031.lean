import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node027
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node030

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node031Rows : List Row := [[(0,(1)),(6,(-1))],[(1,(1)),(7,(-1))],[(2,(1)),(7,(1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(-1))]]
def node031Reduction : Bool→Reduction := fun t=>if t then { rows := node030Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(3,(-1)),(5,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node027Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 2, weights := [(1,(1)),(5,(1))] },{ denominator := 2, weights := [(1,(1)),(2,(2)),(5,(-1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(1,(-1)),(4,(2)),(5,(1))] },{ denominator := 2, weights := [(1,(-1)),(5,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node031Covers : Covers node031Rows := by
  apply covers_split _ 5 node031Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node027Covers
    · exact node030Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
