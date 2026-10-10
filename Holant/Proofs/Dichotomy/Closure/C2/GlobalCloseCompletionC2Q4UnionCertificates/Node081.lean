import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node076
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node080

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node081Rows : List Row := [[(0,(1)),(6,(-1))],[(4,(1)),(7,(1))],[(5,(1)),(6,(1))]]
def node081Reduction : Bool→Reduction := fun t=>if t then { rows := node080Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node076Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(-1)),(3,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node081Covers : Covers node081Rows := by
  apply covers_split _ 3 node081Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node076Covers
    · exact node080Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
