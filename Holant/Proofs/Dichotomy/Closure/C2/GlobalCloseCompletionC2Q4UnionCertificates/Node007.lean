import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node007Rows : List Row := [[(0,(1))],[(1,(1))],[(2,(1))],[(3,(1))],[(4,(1))],[(5,(1))],[(7,(1))]]
def node007Reduction : Reduction := { rows := targetRows 0, witnesses := fun i => ([{ denominator := 1, weights := [(1,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(6,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node007Covers : Covers node007Rows := covers_accept _ 0 node007Reduction rfl (by decide +kernel)

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
