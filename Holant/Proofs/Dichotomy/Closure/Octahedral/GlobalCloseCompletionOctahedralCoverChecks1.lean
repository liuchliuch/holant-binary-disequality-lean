import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_3 : ∀j k : Fin 24,
    (3 : Fin 24)∈planeMask (planeCode 3 j k) ∧ j∈planeMask (planeCode 3 j k) ∧ k∈planeMask (planeCode 3 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_4 : ∀j k : Fin 24,
    (4 : Fin 24)∈planeMask (planeCode 4 j k) ∧ j∈planeMask (planeCode 4 j k) ∧ k∈planeMask (planeCode 4 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_5 : ∀j k : Fin 24,
    (5 : Fin 24)∈planeMask (planeCode 5 j k) ∧ j∈planeMask (planeCode 5 j k) ∧ k∈planeMask (planeCode 5 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
