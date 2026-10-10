import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMData
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues.Value6
open GlobalCloseCompletionKleinEightRMData
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
theorem at0 : ∀x : Fin 8→Bool,source 6 0 (word 6 0 x)=2*correction 6 x*rm x := by decide +kernel
theorem at1 : ∀x : Fin 8→Bool,source 6 1 (word 6 1 x)=2*correction 6 x*rm x := by decide +kernel
theorem at2 : ∀x : Fin 8→Bool,source 6 2 (word 6 2 x)=2*correction 6 x*rm x := by decide +kernel
theorem at3 : ∀x : Fin 8→Bool,source 6 3 (word 6 3 x)=2*correction 6 x*rm x := by decide +kernel
theorem at4 : ∀x : Fin 8→Bool,source 6 4 (word 6 4 x)=2*correction 6 x*rm x := by decide +kernel
theorem at5 : ∀x : Fin 8→Bool,source 6 5 (word 6 5 x)=2*correction 6 x*rm x := by decide +kernel
theorem at6 : ∀x : Fin 8→Bool,source 6 6 (word 6 6 x)=2*correction 6 x*rm x := by decide +kernel
theorem at7 : ∀x : Fin 8→Bool,source 6 7 (word 6 7 x)=2*correction 6 x*rm x := by decide +kernel
theorem value : ∀b : Fin 8,∀x : Fin 8→Bool,source 6 b (word 6 b x)=2*correction 6 x*rm x := by
  intro b
  fin_cases b
  · exact at0
  · exact at1
  · exact at2
  · exact at3
  · exact at4
  · exact at5
  · exact at6
  · exact at7

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues.Value6
