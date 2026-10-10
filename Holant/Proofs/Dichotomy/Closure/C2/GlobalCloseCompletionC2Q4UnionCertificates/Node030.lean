import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node028
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node029

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node030Rows : List Row := [[(0,(1)),(6,(-1))],[(1,(1)),(7,(-1))],[(2,(1)),(7,(1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(-1))],[(5,(1)),(6,(-1))]]
def node030Reduction : Bool→Reduction := fun t=>if t then { rows := node029Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 2, weights := [(1,(1)),(6,(1))] },{ denominator := 2, weights := [(1,(1)),(2,(2)),(6,(-1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(1,(-1)),(4,(2)),(6,(1))] },{ denominator := 1, weights := [(5,(1))] },{ denominator := 2, weights := [(1,(-1)),(6,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node028Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(1)),(6,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 2, weights := [(0,(1)),(3,(2)),(6,(-1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 2, weights := [(0,(-1)),(5,(2)),(6,(1))] },{ denominator := 2, weights := [(0,(-1)),(6,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node030Covers : Covers node030Rows := by
  apply covers_split _ 6 node030Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node028Covers
    · exact node029Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
