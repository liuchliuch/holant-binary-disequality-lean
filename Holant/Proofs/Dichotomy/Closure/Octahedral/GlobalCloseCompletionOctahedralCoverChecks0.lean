import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_0 : ∀j k : Fin 24,
    (0 : Fin 24)∈planeMask (planeCode 0 j k) ∧ j∈planeMask (planeCode 0 j k) ∧ k∈planeMask (planeCode 0 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_1 : ∀j k : Fin 24,
    (1 : Fin 24)∈planeMask (planeCode 1 j k) ∧ j∈planeMask (planeCode 1 j k) ∧ k∈planeMask (planeCode 1 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_2 : ∀j k : Fin 24,
    (2 : Fin 24)∈planeMask (planeCode 2 j k) ∧ j∈planeMask (planeCode 2 j k) ∧ k∈planeMask (planeCode 2 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
