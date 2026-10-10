import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node081
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node097

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node098Rows : List Row := [[(4,(1)),(7,(1))],[(5,(1)),(6,(1))]]
def node098Reduction : Bool→Reduction := fun t=>if t then { rows := node097Rows, witnesses := fun i => ([{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node081Rows, witnesses := fun i => ([{ denominator := 1, weights := [(1,(-1)),(2,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node098Covers : Covers node098Rows := by
  apply covers_split _ 2 node098Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node081Covers
    · exact node097Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
