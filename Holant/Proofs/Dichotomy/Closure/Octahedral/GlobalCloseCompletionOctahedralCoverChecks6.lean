import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneData
set_option maxHeartbeats 30000000
set_option maxRecDepth 1000000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
theorem plane_cover_18 : ∀j k : Fin 24,
    (18 : Fin 24)∈planeMask (planeCode 18 j k) ∧ j∈planeMask (planeCode 18 j k) ∧ k∈planeMask (planeCode 18 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_19 : ∀j k : Fin 24,
    (19 : Fin 24)∈planeMask (planeCode 19 j k) ∧ j∈planeMask (planeCode 19 j k) ∧ k∈planeMask (planeCode 19 j k) := by
  intro j
  fin_cases j <;> decide +kernel
theorem plane_cover_20 : ∀j k : Fin 24,
    (20 : Fin 24)∈planeMask (planeCode 20 j k) ∧ j∈planeMask (planeCode 20 j k) ∧ k∈planeMask (planeCode 20 j k) := by
  intro j
  fin_cases j <;> decide +kernel
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
