import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_15 : ∀j k : Fin 24,
    (15 : Fin 24)∈planeMask (planeCode 15 j k) ∧ j∈planeMask (planeCode 15 j k) ∧ k∈planeMask (planeCode 15 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_16 : ∀j k : Fin 24,
    (16 : Fin 24)∈planeMask (planeCode 16 j k) ∧ j∈planeMask (planeCode 16 j k) ∧ k∈planeMask (planeCode 16 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_17 : ∀j k : Fin 24,
    (17 : Fin 24)∈planeMask (planeCode 17 j k) ∧ j∈planeMask (planeCode 17 j k) ∧ k∈planeMask (planeCode 17 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
