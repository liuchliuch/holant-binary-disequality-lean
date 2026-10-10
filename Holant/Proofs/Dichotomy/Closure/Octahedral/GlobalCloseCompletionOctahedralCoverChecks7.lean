import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_21 : ∀j k : Fin 24,
    (21 : Fin 24)∈planeMask (planeCode 21 j k) ∧ j∈planeMask (planeCode 21 j k) ∧ k∈planeMask (planeCode 21 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_22 : ∀j k : Fin 24,
    (22 : Fin 24)∈planeMask (planeCode 22 j k) ∧ j∈planeMask (planeCode 22 j k) ∧ k∈planeMask (planeCode 22 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_23 : ∀j k : Fin 24,
    (23 : Fin 24)∈planeMask (planeCode 23 j k) ∧ j∈planeMask (planeCode 23 j k) ∧ k∈planeMask (planeCode 23 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
