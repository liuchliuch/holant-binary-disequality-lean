import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_12 : ∀j k : Fin 24,
    (12 : Fin 24)∈planeMask (planeCode 12 j k) ∧ j∈planeMask (planeCode 12 j k) ∧ k∈planeMask (planeCode 12 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_13 : ∀j k : Fin 24,
    (13 : Fin 24)∈planeMask (planeCode 13 j k) ∧ j∈planeMask (planeCode 13 j k) ∧ k∈planeMask (planeCode 13 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_14 : ∀j k : Fin 24,
    (14 : Fin 24)∈planeMask (planeCode 14 j k) ∧ j∈planeMask (planeCode 14 j k) ∧ k∈planeMask (planeCode 14 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
