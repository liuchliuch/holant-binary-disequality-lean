import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node059
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node064

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node065Rows : List Row := [[(1,(1)),(2,(1))],[(4,(1)),(7,(1))]]
def node065Reduction : Bool→Reduction := fun t=>if t then { rows := node064Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1)),(2,(-1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node059Rows, witnesses := fun i => ([{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node065Covers : Covers node065Rows := by
  apply covers_split _ 2 node065Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node059Covers
    · exact node064Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
