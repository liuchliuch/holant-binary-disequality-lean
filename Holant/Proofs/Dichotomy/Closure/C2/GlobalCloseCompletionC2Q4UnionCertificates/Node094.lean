import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node092
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node093

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node094Rows : List Row := [[(2,(1))],[(3,(1))],[(4,(1))],[(5,(1))],[(6,(1))],[(7,(1))]]
def node094Reduction : Bool→Reduction := fun t=>if t then { rows := node093Rows, witnesses := fun i => ([{ denominator := 1, weights := [(5,(-1)),(6,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(5,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node092Rows, witnesses := fun i => ([{ denominator := 1, weights := [(4,(-1)),(6,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(5,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node094Covers : Covers node094Rows := by
  apply covers_split _ 6 node094Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node092Covers
    · exact node093Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
