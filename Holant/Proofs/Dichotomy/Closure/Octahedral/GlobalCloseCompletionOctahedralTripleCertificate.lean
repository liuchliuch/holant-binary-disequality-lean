import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlaneCover
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralTripleChecks0
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
open Holant.Certificates.OctahedralSeparator
/-- Standard-row certificates suffice because both marked Frobenius sides
are transported through their explicitly checked Gram corrections. -/
theorem plane_certificate (f : Form) (p : Fin 120) (hf : f=0) : PlaneCertificate f p := by
  subst f
  exact row_plane_certificate_0 p
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.RankThree
