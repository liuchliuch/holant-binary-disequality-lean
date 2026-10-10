import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_pair_10 : ∀j : Fin 60, (10 : Fin 60)≠j →
    (10 : Fin 60)∈icosahedralSecants (icosahedralPairLine 10 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 10 j) ∧
    (j∈icosahedralNeighbors 10 ↔ 3≤(icosahedralSecants (icosahedralPairLine 10 j)).card) := by decide +kernel

theorem icosahedral_pair_11 : ∀j : Fin 60, (11 : Fin 60)≠j →
    (11 : Fin 60)∈icosahedralSecants (icosahedralPairLine 11 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 11 j) ∧
    (j∈icosahedralNeighbors 11 ↔ 3≤(icosahedralSecants (icosahedralPairLine 11 j)).card) := by decide +kernel

theorem icosahedral_pair_12 : ∀j : Fin 60, (12 : Fin 60)≠j →
    (12 : Fin 60)∈icosahedralSecants (icosahedralPairLine 12 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 12 j) ∧
    (j∈icosahedralNeighbors 12 ↔ 3≤(icosahedralSecants (icosahedralPairLine 12 j)).card) := by decide +kernel

theorem icosahedral_pair_13 : ∀j : Fin 60, (13 : Fin 60)≠j →
    (13 : Fin 60)∈icosahedralSecants (icosahedralPairLine 13 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 13 j) ∧
    (j∈icosahedralNeighbors 13 ↔ 3≤(icosahedralSecants (icosahedralPairLine 13 j)).card) := by decide +kernel

theorem icosahedral_pair_14 : ∀j : Fin 60, (14 : Fin 60)≠j →
    (14 : Fin 60)∈icosahedralSecants (icosahedralPairLine 14 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 14 j) ∧
    (j∈icosahedralNeighbors 14 ↔ 3≤(icosahedralSecants (icosahedralPairLine 14 j)).card) := by decide +kernel

theorem icosahedral_pair_15 : ∀j : Fin 60, (15 : Fin 60)≠j →
    (15 : Fin 60)∈icosahedralSecants (icosahedralPairLine 15 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 15 j) ∧
    (j∈icosahedralNeighbors 15 ↔ 3≤(icosahedralSecants (icosahedralPairLine 15 j)).card) := by decide +kernel

theorem icosahedral_pair_16 : ∀j : Fin 60, (16 : Fin 60)≠j →
    (16 : Fin 60)∈icosahedralSecants (icosahedralPairLine 16 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 16 j) ∧
    (j∈icosahedralNeighbors 16 ↔ 3≤(icosahedralSecants (icosahedralPairLine 16 j)).card) := by decide +kernel

theorem icosahedral_pair_17 : ∀j : Fin 60, (17 : Fin 60)≠j →
    (17 : Fin 60)∈icosahedralSecants (icosahedralPairLine 17 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 17 j) ∧
    (j∈icosahedralNeighbors 17 ↔ 3≤(icosahedralSecants (icosahedralPairLine 17 j)).card) := by decide +kernel

theorem icosahedral_pair_18 : ∀j : Fin 60, (18 : Fin 60)≠j →
    (18 : Fin 60)∈icosahedralSecants (icosahedralPairLine 18 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 18 j) ∧
    (j∈icosahedralNeighbors 18 ↔ 3≤(icosahedralSecants (icosahedralPairLine 18 j)).card) := by decide +kernel

theorem icosahedral_pair_19 : ∀j : Fin 60, (19 : Fin 60)≠j →
    (19 : Fin 60)∈icosahedralSecants (icosahedralPairLine 19 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 19 j) ∧
    (j∈icosahedralNeighbors 19 ↔ 3≤(icosahedralSecants (icosahedralPairLine 19 j)).card) := by decide +kernel


end Holant.Certificates.PlatonicIncidence
