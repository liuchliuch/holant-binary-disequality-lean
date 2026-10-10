import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMData
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues.Value0
open GlobalCloseCompletionKleinEightRMData
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
theorem value : ∀b : Fin 8,∀x : Fin 8→Bool,
    source 0 b (word 0 b x)=2*correction 0 x*rm x := by decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues.Value0
