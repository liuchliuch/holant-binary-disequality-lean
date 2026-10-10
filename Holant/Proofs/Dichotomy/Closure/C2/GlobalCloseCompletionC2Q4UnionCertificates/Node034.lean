import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node016
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node033

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node034Rows : List Row := [[(0,(1)),(3,(1))],[(1,(1)),(2,(1))]]
def node034Reduction : Bool→Reduction := fun t=>if t then { rows := node033Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1)),(2,(-1))] },{ denominator := 1, weights := [(2,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node016Rows, witnesses := fun i => ([{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(0,(1)),(2,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node034Covers : Covers node034Rows := by
  apply covers_split _ 2 node034Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node016Covers
    · exact node033Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
