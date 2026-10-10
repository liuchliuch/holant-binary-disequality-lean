import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node021
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node032

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node033Rows : List Row := [[(0,(1)),(3,(1))],[(1,(1)),(7,(-1))],[(2,(1)),(7,(1))]]
def node033Reduction : Bool→Reduction := fun t=>if t then { rows := node032Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1)),(3,(-1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node021Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(1,(-1)),(3,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node033Covers : Covers node033Rows := by
  apply covers_split _ 3 node033Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node021Covers
    · exact node032Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
