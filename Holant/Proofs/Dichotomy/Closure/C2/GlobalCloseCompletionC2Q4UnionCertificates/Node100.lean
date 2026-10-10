import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Union
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node050
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node099

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def node100Rows : List Row := []
def node100Reduction : Bool→Reduction := fun t=>if t then { rows := node099Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } } else { rows := node050Rows, witnesses := fun i => ([{ denominator := 1, weights := [(0,(1))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }
theorem node100Covers : Covers node100Rows := by
  apply covers_split _ 0 node100Reduction
  · decide +kernel
  · intro t
    cases t
    · exact node050Covers
    · exact node099Covers

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
