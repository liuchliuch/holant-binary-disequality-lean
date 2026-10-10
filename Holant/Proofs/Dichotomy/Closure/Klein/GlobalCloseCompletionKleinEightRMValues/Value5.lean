import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinEightRMData
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues.Value5
open GlobalCloseCompletionKleinEightRMData
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
theorem at0 : ∀x : Fin 8→Bool,source 5 0 (word 5 0 x)=2*correction 5 x*rm x := by decide +kernel
theorem at1 : ∀x : Fin 8→Bool,source 5 1 (word 5 1 x)=2*correction 5 x*rm x := by decide +kernel
theorem at2 : ∀x : Fin 8→Bool,source 5 2 (word 5 2 x)=2*correction 5 x*rm x := by decide +kernel
theorem at3 : ∀x : Fin 8→Bool,source 5 3 (word 5 3 x)=2*correction 5 x*rm x := by decide +kernel
theorem at4 : ∀x : Fin 8→Bool,source 5 4 (word 5 4 x)=2*correction 5 x*rm x := by decide +kernel
theorem at5 : ∀x : Fin 8→Bool,source 5 5 (word 5 5 x)=2*correction 5 x*rm x := by decide +kernel
theorem at6 : ∀x : Fin 8→Bool,source 5 6 (word 5 6 x)=2*correction 5 x*rm x := by decide +kernel
theorem at7 : ∀x : Fin 8→Bool,source 5 7 (word 5 7 x)=2*correction 5 x*rm x := by decide +kernel
theorem value : ∀b : Fin 8,∀x : Fin 8→Bool,source 5 b (word 5 b x)=2*correction 5 x*rm x := by
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

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinEightRMValues.Value5
