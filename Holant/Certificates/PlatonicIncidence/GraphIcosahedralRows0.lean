import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_pair_0 : ∀j : Fin 60, (0 : Fin 60)≠j →
    (0 : Fin 60)∈icosahedralSecants (icosahedralPairLine 0 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 0 j) ∧
    (j∈icosahedralNeighbors 0 ↔ 3≤(icosahedralSecants (icosahedralPairLine 0 j)).card) := by decide +kernel

theorem icosahedral_pair_1 : ∀j : Fin 60, (1 : Fin 60)≠j →
    (1 : Fin 60)∈icosahedralSecants (icosahedralPairLine 1 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 1 j) ∧
    (j∈icosahedralNeighbors 1 ↔ 3≤(icosahedralSecants (icosahedralPairLine 1 j)).card) := by decide +kernel

theorem icosahedral_pair_2 : ∀j : Fin 60, (2 : Fin 60)≠j →
    (2 : Fin 60)∈icosahedralSecants (icosahedralPairLine 2 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 2 j) ∧
    (j∈icosahedralNeighbors 2 ↔ 3≤(icosahedralSecants (icosahedralPairLine 2 j)).card) := by decide +kernel

theorem icosahedral_pair_3 : ∀j : Fin 60, (3 : Fin 60)≠j →
    (3 : Fin 60)∈icosahedralSecants (icosahedralPairLine 3 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 3 j) ∧
    (j∈icosahedralNeighbors 3 ↔ 3≤(icosahedralSecants (icosahedralPairLine 3 j)).card) := by decide +kernel

theorem icosahedral_pair_4 : ∀j : Fin 60, (4 : Fin 60)≠j →
    (4 : Fin 60)∈icosahedralSecants (icosahedralPairLine 4 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 4 j) ∧
    (j∈icosahedralNeighbors 4 ↔ 3≤(icosahedralSecants (icosahedralPairLine 4 j)).card) := by decide +kernel

theorem icosahedral_pair_5 : ∀j : Fin 60, (5 : Fin 60)≠j →
    (5 : Fin 60)∈icosahedralSecants (icosahedralPairLine 5 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 5 j) ∧
    (j∈icosahedralNeighbors 5 ↔ 3≤(icosahedralSecants (icosahedralPairLine 5 j)).card) := by decide +kernel

theorem icosahedral_pair_6 : ∀j : Fin 60, (6 : Fin 60)≠j →
    (6 : Fin 60)∈icosahedralSecants (icosahedralPairLine 6 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 6 j) ∧
    (j∈icosahedralNeighbors 6 ↔ 3≤(icosahedralSecants (icosahedralPairLine 6 j)).card) := by decide +kernel

theorem icosahedral_pair_7 : ∀j : Fin 60, (7 : Fin 60)≠j →
    (7 : Fin 60)∈icosahedralSecants (icosahedralPairLine 7 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 7 j) ∧
    (j∈icosahedralNeighbors 7 ↔ 3≤(icosahedralSecants (icosahedralPairLine 7 j)).card) := by decide +kernel

theorem icosahedral_pair_8 : ∀j : Fin 60, (8 : Fin 60)≠j →
    (8 : Fin 60)∈icosahedralSecants (icosahedralPairLine 8 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 8 j) ∧
    (j∈icosahedralNeighbors 8 ↔ 3≤(icosahedralSecants (icosahedralPairLine 8 j)).card) := by decide +kernel

theorem icosahedral_pair_9 : ∀j : Fin 60, (9 : Fin 60)≠j →
    (9 : Fin 60)∈icosahedralSecants (icosahedralPairLine 9 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 9 j) ∧
    (j∈icosahedralNeighbors 9 ↔ 3≤(icosahedralSecants (icosahedralPairLine 9 j)).card) := by decide +kernel


end Holant.Certificates.PlatonicIncidence
