import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node035
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node038

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node039Rows : List Row := [[(0,(1)),(6,(-1))],[(3,(1)),(6,(1))],[(5,(1)),(6,(1))]]
def node039Reduction : Bool→Reduction := fun t=>if t then { rows := node038Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node035Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(1)),(3,(1))] },{ denominator := 2, weights := [(0,(1)),(1,(2)),(3,(-1))] },{ denominator := 2, weights := [(0,(1)),(2,(2)),(3,(-1))] },{ denominator := 2, weights := [(0,(-1)),(3,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node039Covers : Covers node039Rows := by
  apply covers_split _ 4 node039Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node035Covers
    · exact node038Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
