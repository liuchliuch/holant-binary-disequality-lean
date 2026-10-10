import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node086
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node087

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node088Rows : List Row := [[(0,(1)),(6,(1))],[(1,(1)),(7,(1))],[(2,(1)),(7,(1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(1))],[(5,(1)),(6,(1))]]
def node088Reduction : Bool→Reduction := fun t=>if t then { rows := node087Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(2)),(3,(-1)),(5,(-1)),(6,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 2, weights := [(3,(1)),(5,(-1)),(6,(1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 2, weights := [(3,(-1)),(5,(1)),(6,(1))] },{ denominator := 2, weights := [(3,(1)),(5,(1)),(6,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node086Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 2, weights := [(1,(2)),(2,(-1)),(4,(-1)),(6,(1))] },{ denominator := 2, weights := [(2,(1)),(4,(-1)),(6,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(2,(-1)),(4,(1)),(6,(1))] },{ denominator := 1, weights := [(5,(1))] },{ denominator := 2, weights := [(2,(1)),(4,(1)),(6,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node088Covers : Covers node088Rows := by
  apply covers_split _ 7 node088Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node086Covers
    · exact node087Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
