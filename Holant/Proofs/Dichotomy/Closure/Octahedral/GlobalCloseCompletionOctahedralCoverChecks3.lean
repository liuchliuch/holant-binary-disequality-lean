import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_9 : ∀j k : Fin 24,
    (9 : Fin 24)∈planeMask (planeCode 9 j k) ∧ j∈planeMask (planeCode 9 j k) ∧ k∈planeMask (planeCode 9 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_10 : ∀j k : Fin 24,
    (10 : Fin 24)∈planeMask (planeCode 10 j k) ∧ j∈planeMask (planeCode 10 j k) ∧ k∈planeMask (planeCode 10 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_11 : ∀j k : Fin 24,
    (11 : Fin 24)∈planeMask (planeCode 11 j k) ∧ j∈planeMask (planeCode 11 j k) ∧ k∈planeMask (planeCode 11 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
