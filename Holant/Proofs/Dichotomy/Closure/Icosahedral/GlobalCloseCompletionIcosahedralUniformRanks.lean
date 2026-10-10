import Holant.Certificates.IcosahedralSeparator.UniformSemanticBridge

/-! Only the thirty exact rank witnesses needed by the current six-port
I exclusion are checked here. The original uniform kernel, coefficient
code and selected minors remain unchanged. -/
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.UniformRanks
open Holant.Certificates.IcosahedralSeparator

theorem rank_checks (i : Fin 30) : UniformRankCheck i := by
  fin_cases i <;> decide +kernel

noncomputable section
theorem output_ranks (i : Fin 30) (r : Fin 3) :
    (Holant.Certificates.MatchingProductBridge.flatten r (uniformOutput i)).rank=3 :=
  uniform_rank_three_of_check i (rank_checks i) r

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.UniformRanks
