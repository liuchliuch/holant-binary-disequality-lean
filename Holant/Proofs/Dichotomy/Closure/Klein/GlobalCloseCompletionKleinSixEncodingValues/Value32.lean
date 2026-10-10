import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixEncoding
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixEncodingValues.Value32
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
theorem value : ∀a : Fin 48,∀k : Fin 4,
    GlobalCloseCompletionKleinSixEncoding.coefficient 3 a 2 k=
      GlobalCloseCompletionKleinSixLinearPacked.coefficient 3 a 2 k := by decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixEncodingValues.Value32
