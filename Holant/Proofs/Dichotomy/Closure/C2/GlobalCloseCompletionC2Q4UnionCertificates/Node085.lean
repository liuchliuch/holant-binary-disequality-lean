import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node083
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node084

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node085Rows : List Row := [[(1,(1)),(7,(-1))],[(2,(1)),(7,(1))],[(4,(1)),(7,(1))],[(5,(1)),(6,(1))]]
def node085Reduction : Bool→Reduction := fun t=>if t then { rows := node084Rows, witnesses := fun i => ([{ denominator := 2, weights := [(0,(2)),(1,(1)),(2,(1)),(4,(-1))] },{ denominator := 2, weights := [(1,(1)),(2,(-1)),(4,(1))] },{ denominator := 2, weights := [(1,(-1)),(2,(1)),(4,(1))] },{ denominator := 1, weights := [(3,(1))] },{ denominator := 2, weights := [(1,(1)),(2,(1)),(4,(-1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node083Rows, witnesses := fun i => ([{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(3,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node085Covers : Covers node085Rows := by
  apply covers_split _ 4 node085Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node083Covers
    · exact node084Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
