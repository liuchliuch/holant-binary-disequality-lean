import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_6 : ∀j k : Fin 24,
    (6 : Fin 24)∈planeMask (planeCode 6 j k) ∧ j∈planeMask (planeCode 6 j k) ∧ k∈planeMask (planeCode 6 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_7 : ∀j k : Fin 24,
    (7 : Fin 24)∈planeMask (planeCode 7 j k) ∧ j∈planeMask (planeCode 7 j k) ∧ k∈planeMask (planeCode 7 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_8 : ∀j k : Fin 24,
    (8 : Fin 24)∈planeMask (planeCode 8 j k) ∧ j∈planeMask (planeCode 8 j k) ∧ k∈planeMask (planeCode 8 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
