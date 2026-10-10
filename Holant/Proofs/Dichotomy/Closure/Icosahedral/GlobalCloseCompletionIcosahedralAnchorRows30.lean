import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralAnchorData

set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree

theorem anchor_row30 : ∀ c : Fin 31, finiteCertificate 30 c := by
  intro c; fin_cases c <;> decide +kernel

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
