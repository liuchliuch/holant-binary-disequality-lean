import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_pair_30 : ∀j : Fin 60, (30 : Fin 60)≠j →
    (30 : Fin 60)∈icosahedralSecants (icosahedralPairLine 30 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 30 j) ∧
    (j∈icosahedralNeighbors 30 ↔ 3≤(icosahedralSecants (icosahedralPairLine 30 j)).card) := by decide +kernel

theorem icosahedral_pair_31 : ∀j : Fin 60, (31 : Fin 60)≠j →
    (31 : Fin 60)∈icosahedralSecants (icosahedralPairLine 31 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 31 j) ∧
    (j∈icosahedralNeighbors 31 ↔ 3≤(icosahedralSecants (icosahedralPairLine 31 j)).card) := by decide +kernel

theorem icosahedral_pair_32 : ∀j : Fin 60, (32 : Fin 60)≠j →
    (32 : Fin 60)∈icosahedralSecants (icosahedralPairLine 32 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 32 j) ∧
    (j∈icosahedralNeighbors 32 ↔ 3≤(icosahedralSecants (icosahedralPairLine 32 j)).card) := by decide +kernel

theorem icosahedral_pair_33 : ∀j : Fin 60, (33 : Fin 60)≠j →
    (33 : Fin 60)∈icosahedralSecants (icosahedralPairLine 33 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 33 j) ∧
    (j∈icosahedralNeighbors 33 ↔ 3≤(icosahedralSecants (icosahedralPairLine 33 j)).card) := by decide +kernel

theorem icosahedral_pair_34 : ∀j : Fin 60, (34 : Fin 60)≠j →
    (34 : Fin 60)∈icosahedralSecants (icosahedralPairLine 34 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 34 j) ∧
    (j∈icosahedralNeighbors 34 ↔ 3≤(icosahedralSecants (icosahedralPairLine 34 j)).card) := by decide +kernel

theorem icosahedral_pair_35 : ∀j : Fin 60, (35 : Fin 60)≠j →
    (35 : Fin 60)∈icosahedralSecants (icosahedralPairLine 35 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 35 j) ∧
    (j∈icosahedralNeighbors 35 ↔ 3≤(icosahedralSecants (icosahedralPairLine 35 j)).card) := by decide +kernel

theorem icosahedral_pair_36 : ∀j : Fin 60, (36 : Fin 60)≠j →
    (36 : Fin 60)∈icosahedralSecants (icosahedralPairLine 36 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 36 j) ∧
    (j∈icosahedralNeighbors 36 ↔ 3≤(icosahedralSecants (icosahedralPairLine 36 j)).card) := by decide +kernel

theorem icosahedral_pair_37 : ∀j : Fin 60, (37 : Fin 60)≠j →
    (37 : Fin 60)∈icosahedralSecants (icosahedralPairLine 37 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 37 j) ∧
    (j∈icosahedralNeighbors 37 ↔ 3≤(icosahedralSecants (icosahedralPairLine 37 j)).card) := by decide +kernel

theorem icosahedral_pair_38 : ∀j : Fin 60, (38 : Fin 60)≠j →
    (38 : Fin 60)∈icosahedralSecants (icosahedralPairLine 38 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 38 j) ∧
    (j∈icosahedralNeighbors 38 ↔ 3≤(icosahedralSecants (icosahedralPairLine 38 j)).card) := by decide +kernel

theorem icosahedral_pair_39 : ∀j : Fin 60, (39 : Fin 60)≠j →
    (39 : Fin 60)∈icosahedralSecants (icosahedralPairLine 39 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 39 j) ∧
    (j∈icosahedralNeighbors 39 ↔ 3≤(icosahedralSecants (icosahedralPairLine 39 j)).card) := by decide +kernel


end Holant.Certificates.PlatonicIncidence
