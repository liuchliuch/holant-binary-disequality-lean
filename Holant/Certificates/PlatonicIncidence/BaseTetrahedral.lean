import Holant.Certificates.PlatonicIncidence.BaseData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem tetrahedral_base_1 : baseSecant .tetrahedral (1 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (1 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_2 : baseSecant .tetrahedral (2 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (2 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_3 : baseSecant .tetrahedral (3 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (3 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_4 : baseSecant .tetrahedral (4 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (4 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_5 : baseSecant .tetrahedral (5 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (5 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_6 : baseSecant .tetrahedral (6 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (6 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_7 : baseSecant .tetrahedral (7 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (7 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_8 : baseSecant .tetrahedral (8 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (8 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_9 : baseSecant .tetrahedral (9 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (9 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_10 : baseSecant .tetrahedral (10 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (10 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_base_11 : baseSecant .tetrahedral (11 : Fin 12)=baseLine .tetrahedral (baseLineOf .tetrahedral (11 : Fin 12)) := by
  decide +kernel

theorem tetrahedral_anchors : ∀ b : Fin 7,
    baseAnchor .tetrahedral b≠identityIndex .tetrahedral ∧
    baseLineOf .tetrahedral (baseAnchor .tetrahedral b)=b ∧
    identityIndex .tetrahedral∈baseLine .tetrahedral b ∧
    baseAnchor .tetrahedral b∈baseLine .tetrahedral b := by
  change ∀ b : Fin 7, tetrahedralAnchor b≠(0 : Fin 12) ∧
    tetrahedralLineOf (tetrahedralAnchor b)=b ∧
    (0 : Fin 12)∈tetrahedralLines b ∧ tetrahedralAnchor b∈tetrahedralLines b
  decide +kernel

end Holant.Certificates.PlatonicIncidence
