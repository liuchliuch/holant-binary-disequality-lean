import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node067Rows : List Row := [[(0,(1))],[(1,(1))],[(3,(1))],[(4,(1))],[(5,(1))],[(6,(1))],[(7,(1))]]
def node067Reduction : Reduction := { rows := targetRows 1, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] },{ denominator := 1, weights := [(2,(1))] },{ denominator := 1, weights := [(4,(1))] },{ denominator := 1, weights := [(5,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node067Covers : Covers node067Rows := covers_accept _ 1 node067Reduction rfl (by decide +kernel)

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
