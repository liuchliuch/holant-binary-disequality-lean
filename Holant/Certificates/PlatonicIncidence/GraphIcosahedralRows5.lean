import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_pair_50 : ∀j : Fin 60, (50 : Fin 60)≠j →
    (50 : Fin 60)∈icosahedralSecants (icosahedralPairLine 50 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 50 j) ∧
    (j∈icosahedralNeighbors 50 ↔ 3≤(icosahedralSecants (icosahedralPairLine 50 j)).card) := by decide +kernel

theorem icosahedral_pair_51 : ∀j : Fin 60, (51 : Fin 60)≠j →
    (51 : Fin 60)∈icosahedralSecants (icosahedralPairLine 51 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 51 j) ∧
    (j∈icosahedralNeighbors 51 ↔ 3≤(icosahedralSecants (icosahedralPairLine 51 j)).card) := by decide +kernel

theorem icosahedral_pair_52 : ∀j : Fin 60, (52 : Fin 60)≠j →
    (52 : Fin 60)∈icosahedralSecants (icosahedralPairLine 52 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 52 j) ∧
    (j∈icosahedralNeighbors 52 ↔ 3≤(icosahedralSecants (icosahedralPairLine 52 j)).card) := by decide +kernel

theorem icosahedral_pair_53 : ∀j : Fin 60, (53 : Fin 60)≠j →
    (53 : Fin 60)∈icosahedralSecants (icosahedralPairLine 53 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 53 j) ∧
    (j∈icosahedralNeighbors 53 ↔ 3≤(icosahedralSecants (icosahedralPairLine 53 j)).card) := by decide +kernel

theorem icosahedral_pair_54 : ∀j : Fin 60, (54 : Fin 60)≠j →
    (54 : Fin 60)∈icosahedralSecants (icosahedralPairLine 54 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 54 j) ∧
    (j∈icosahedralNeighbors 54 ↔ 3≤(icosahedralSecants (icosahedralPairLine 54 j)).card) := by decide +kernel

theorem icosahedral_pair_55 : ∀j : Fin 60, (55 : Fin 60)≠j →
    (55 : Fin 60)∈icosahedralSecants (icosahedralPairLine 55 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 55 j) ∧
    (j∈icosahedralNeighbors 55 ↔ 3≤(icosahedralSecants (icosahedralPairLine 55 j)).card) := by decide +kernel

theorem icosahedral_pair_56 : ∀j : Fin 60, (56 : Fin 60)≠j →
    (56 : Fin 60)∈icosahedralSecants (icosahedralPairLine 56 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 56 j) ∧
    (j∈icosahedralNeighbors 56 ↔ 3≤(icosahedralSecants (icosahedralPairLine 56 j)).card) := by decide +kernel

theorem icosahedral_pair_57 : ∀j : Fin 60, (57 : Fin 60)≠j →
    (57 : Fin 60)∈icosahedralSecants (icosahedralPairLine 57 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 57 j) ∧
    (j∈icosahedralNeighbors 57 ↔ 3≤(icosahedralSecants (icosahedralPairLine 57 j)).card) := by decide +kernel

theorem icosahedral_pair_58 : ∀j : Fin 60, (58 : Fin 60)≠j →
    (58 : Fin 60)∈icosahedralSecants (icosahedralPairLine 58 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 58 j) ∧
    (j∈icosahedralNeighbors 58 ↔ 3≤(icosahedralSecants (icosahedralPairLine 58 j)).card) := by decide +kernel

theorem icosahedral_pair_59 : ∀j : Fin 60, (59 : Fin 60)≠j →
    (59 : Fin 60)∈icosahedralSecants (icosahedralPairLine 59 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 59 j) ∧
    (j∈icosahedralNeighbors 59 ↔ 3≤(icosahedralSecants (icosahedralPairLine 59 j)).card) := by decide +kernel


end Holant.Certificates.PlatonicIncidence
