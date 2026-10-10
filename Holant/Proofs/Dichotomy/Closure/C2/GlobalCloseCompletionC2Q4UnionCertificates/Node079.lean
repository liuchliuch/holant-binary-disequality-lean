import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node012
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node078

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node079Rows : List Row := [[(0,(1)),(6,(-1))],[(2,(1)),(7,(-1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(1))],[(5,(1)),(6,(1))]]
def node079Reduction : Bool→Reduction := fun t=>if t then { rows := node078Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(2)),(2,(1)),(4,(1)),(5,(-1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 2, weights := [(2,(1)),(4,(-1)),(5,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(2,(-1)),(4,(1)),(5,(1))] },{ denominator := 2, weights := [(2,(1)),(4,(1)),(5,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node012Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(5,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(4,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node079Covers : Covers node079Rows := by
  apply covers_split _ 5 node079Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node012Covers
    · exact node078Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
