import Holant.Certificates.PlatonicIncidence.BaseData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem octahedral_base_1 : baseSecant .octahedral (1 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (1 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_2 : baseSecant .octahedral (2 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (2 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_3 : baseSecant .octahedral (3 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (3 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_4 : baseSecant .octahedral (4 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (4 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_5 : baseSecant .octahedral (5 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (5 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_6 : baseSecant .octahedral (6 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (6 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_7 : baseSecant .octahedral (7 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (7 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_8 : baseSecant .octahedral (8 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (8 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_9 : baseSecant .octahedral (9 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (9 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_10 : baseSecant .octahedral (10 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (10 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_11 : baseSecant .octahedral (11 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (11 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_12 : baseSecant .octahedral (12 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (12 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_13 : baseSecant .octahedral (13 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (13 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_14 : baseSecant .octahedral (14 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (14 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_15 : baseSecant .octahedral (15 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (15 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_16 : baseSecant .octahedral (16 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (16 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_17 : baseSecant .octahedral (17 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (17 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_18 : baseSecant .octahedral (18 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (18 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_19 : baseSecant .octahedral (19 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (19 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_20 : baseSecant .octahedral (20 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (20 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_21 : baseSecant .octahedral (21 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (21 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_22 : baseSecant .octahedral (22 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (22 : Fin 24)) := by
  decide +kernel

theorem octahedral_base_23 : baseSecant .octahedral (23 : Fin 24)=baseLine .octahedral (baseLineOf .octahedral (23 : Fin 24)) := by
  decide +kernel

theorem octahedral_anchors : ∀ b : Fin 13,
    baseAnchor .octahedral b≠identityIndex .octahedral ∧
    baseLineOf .octahedral (baseAnchor .octahedral b)=b ∧
    identityIndex .octahedral∈baseLine .octahedral b ∧
    baseAnchor .octahedral b∈baseLine .octahedral b := by
  change ∀ b : Fin 13, octahedralAnchor b≠(0 : Fin 24) ∧
    octahedralLineOf (octahedralAnchor b)=b ∧
    (0 : Fin 24)∈octahedralLines b ∧ octahedralAnchor b∈octahedralLines b
  decide +kernel

end Holant.Certificates.PlatonicIncidence
