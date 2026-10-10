import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node091
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node094

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node095Rows : List Row := [[(2,(1))],[(3,(1)),(6,(1))],[(4,(1))],[(5,(1)),(6,(1))],[(7,(1))]]
def node095Reduction : Bool→Reduction := fun t=>if t then { rows := node094Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 2, weights := [(1,(1)),(3,(-1)),(5,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 2, weights := [(1,(-1)),(3,(1)),(5,(1))] },{ denominator := 2, weights := [(1,(1)),(3,(1)),(5,(-1))] },{ denominator := 1, weights := [(4,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node091Rows, witnesses := fun i => ([{ denominator := 1, weights := [(4,(-1)),(5,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(4,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node095Covers : Covers node095Rows := by
  apply covers_split _ 5 node095Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node091Covers
    · exact node094Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
