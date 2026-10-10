import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_pair_20 : ∀j : Fin 60, (20 : Fin 60)≠j →
    (20 : Fin 60)∈icosahedralSecants (icosahedralPairLine 20 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 20 j) ∧
    (j∈icosahedralNeighbors 20 ↔ 3≤(icosahedralSecants (icosahedralPairLine 20 j)).card) := by decide +kernel

theorem icosahedral_pair_21 : ∀j : Fin 60, (21 : Fin 60)≠j →
    (21 : Fin 60)∈icosahedralSecants (icosahedralPairLine 21 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 21 j) ∧
    (j∈icosahedralNeighbors 21 ↔ 3≤(icosahedralSecants (icosahedralPairLine 21 j)).card) := by decide +kernel

theorem icosahedral_pair_22 : ∀j : Fin 60, (22 : Fin 60)≠j →
    (22 : Fin 60)∈icosahedralSecants (icosahedralPairLine 22 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 22 j) ∧
    (j∈icosahedralNeighbors 22 ↔ 3≤(icosahedralSecants (icosahedralPairLine 22 j)).card) := by decide +kernel

theorem icosahedral_pair_23 : ∀j : Fin 60, (23 : Fin 60)≠j →
    (23 : Fin 60)∈icosahedralSecants (icosahedralPairLine 23 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 23 j) ∧
    (j∈icosahedralNeighbors 23 ↔ 3≤(icosahedralSecants (icosahedralPairLine 23 j)).card) := by decide +kernel

theorem icosahedral_pair_24 : ∀j : Fin 60, (24 : Fin 60)≠j →
    (24 : Fin 60)∈icosahedralSecants (icosahedralPairLine 24 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 24 j) ∧
    (j∈icosahedralNeighbors 24 ↔ 3≤(icosahedralSecants (icosahedralPairLine 24 j)).card) := by decide +kernel

theorem icosahedral_pair_25 : ∀j : Fin 60, (25 : Fin 60)≠j →
    (25 : Fin 60)∈icosahedralSecants (icosahedralPairLine 25 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 25 j) ∧
    (j∈icosahedralNeighbors 25 ↔ 3≤(icosahedralSecants (icosahedralPairLine 25 j)).card) := by decide +kernel

theorem icosahedral_pair_26 : ∀j : Fin 60, (26 : Fin 60)≠j →
    (26 : Fin 60)∈icosahedralSecants (icosahedralPairLine 26 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 26 j) ∧
    (j∈icosahedralNeighbors 26 ↔ 3≤(icosahedralSecants (icosahedralPairLine 26 j)).card) := by decide +kernel

theorem icosahedral_pair_27 : ∀j : Fin 60, (27 : Fin 60)≠j →
    (27 : Fin 60)∈icosahedralSecants (icosahedralPairLine 27 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 27 j) ∧
    (j∈icosahedralNeighbors 27 ↔ 3≤(icosahedralSecants (icosahedralPairLine 27 j)).card) := by decide +kernel

theorem icosahedral_pair_28 : ∀j : Fin 60, (28 : Fin 60)≠j →
    (28 : Fin 60)∈icosahedralSecants (icosahedralPairLine 28 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 28 j) ∧
    (j∈icosahedralNeighbors 28 ↔ 3≤(icosahedralSecants (icosahedralPairLine 28 j)).card) := by decide +kernel

theorem icosahedral_pair_29 : ∀j : Fin 60, (29 : Fin 60)≠j →
    (29 : Fin 60)∈icosahedralSecants (icosahedralPairLine 29 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 29 j) ∧
    (j∈icosahedralNeighbors 29 ↔ 3≤(icosahedralSecants (icosahedralPairLine 29 j)).card) := by decide +kernel


end Holant.Certificates.PlatonicIncidence
