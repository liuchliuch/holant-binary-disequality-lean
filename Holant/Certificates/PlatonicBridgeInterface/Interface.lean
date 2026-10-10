import Holant.Certificates.PlatonicBridgeInterface.OctahedralClause
import Holant.Certificates.PlatonicBridgeInterface.TetrahedralClause
import Holant.Certificates.PlatonicBridgeInterface.IcosahedralClause

/-! Theorem A.27, the complete Platonic bridge interface. Its three fields
retain unrestricted source normalization, actual complex maps and matrix ranks,
fixed current-group kernels, original-coordinate physical outputs, and the
proved projective A5 isomorphism. No finite-coverage or terminal premise is added. -/
namespace Holant.Certificates.PlatonicBridgeInterface

structure PlatonicBridgeCertificate : Prop where
  octahedral : Octahedral.Clause
  tetrahedral : Tetrahedral.Clause
  icosahedral : Icosahedral.Clause

theorem platonic_bridge_interface : PlatonicBridgeCertificate where
  octahedral := Octahedral.complete_clause
  tetrahedral := Tetrahedral.complete_clause
  icosahedral := Icosahedral.complete_clause

end Holant.Certificates.PlatonicBridgeInterface
