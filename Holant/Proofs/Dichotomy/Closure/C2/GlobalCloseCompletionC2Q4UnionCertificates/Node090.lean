import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node088
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node089

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node090Rows : List Row := [[(0,(1)),(6,(1))],[(2,(1)),(7,(1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(1))],[(5,(1)),(6,(1))]]
def node090Reduction : Bool→Reduction := fun t=>if t then { rows := node089Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(2)),(2,(-1)),(4,(-1)),(5,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 2, weights := [(2,(1)),(4,(-1)),(5,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(2,(-1)),(4,(1)),(5,(1))] },{ denominator := 2, weights := [(2,(1)),(4,(1)),(5,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node088Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(5,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(4,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node090Covers : Covers node090Rows := by
  apply covers_split _ 5 node090Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node088Covers
    · exact node089Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
