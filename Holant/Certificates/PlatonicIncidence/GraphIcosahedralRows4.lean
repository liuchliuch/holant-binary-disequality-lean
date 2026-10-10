import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_pair_40 : ∀j : Fin 60, (40 : Fin 60)≠j →
    (40 : Fin 60)∈icosahedralSecants (icosahedralPairLine 40 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 40 j) ∧
    (j∈icosahedralNeighbors 40 ↔ 3≤(icosahedralSecants (icosahedralPairLine 40 j)).card) := by decide +kernel

theorem icosahedral_pair_41 : ∀j : Fin 60, (41 : Fin 60)≠j →
    (41 : Fin 60)∈icosahedralSecants (icosahedralPairLine 41 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 41 j) ∧
    (j∈icosahedralNeighbors 41 ↔ 3≤(icosahedralSecants (icosahedralPairLine 41 j)).card) := by decide +kernel

theorem icosahedral_pair_42 : ∀j : Fin 60, (42 : Fin 60)≠j →
    (42 : Fin 60)∈icosahedralSecants (icosahedralPairLine 42 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 42 j) ∧
    (j∈icosahedralNeighbors 42 ↔ 3≤(icosahedralSecants (icosahedralPairLine 42 j)).card) := by decide +kernel

theorem icosahedral_pair_43 : ∀j : Fin 60, (43 : Fin 60)≠j →
    (43 : Fin 60)∈icosahedralSecants (icosahedralPairLine 43 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 43 j) ∧
    (j∈icosahedralNeighbors 43 ↔ 3≤(icosahedralSecants (icosahedralPairLine 43 j)).card) := by decide +kernel

theorem icosahedral_pair_44 : ∀j : Fin 60, (44 : Fin 60)≠j →
    (44 : Fin 60)∈icosahedralSecants (icosahedralPairLine 44 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 44 j) ∧
    (j∈icosahedralNeighbors 44 ↔ 3≤(icosahedralSecants (icosahedralPairLine 44 j)).card) := by decide +kernel

theorem icosahedral_pair_45 : ∀j : Fin 60, (45 : Fin 60)≠j →
    (45 : Fin 60)∈icosahedralSecants (icosahedralPairLine 45 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 45 j) ∧
    (j∈icosahedralNeighbors 45 ↔ 3≤(icosahedralSecants (icosahedralPairLine 45 j)).card) := by decide +kernel

theorem icosahedral_pair_46 : ∀j : Fin 60, (46 : Fin 60)≠j →
    (46 : Fin 60)∈icosahedralSecants (icosahedralPairLine 46 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 46 j) ∧
    (j∈icosahedralNeighbors 46 ↔ 3≤(icosahedralSecants (icosahedralPairLine 46 j)).card) := by decide +kernel

theorem icosahedral_pair_47 : ∀j : Fin 60, (47 : Fin 60)≠j →
    (47 : Fin 60)∈icosahedralSecants (icosahedralPairLine 47 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 47 j) ∧
    (j∈icosahedralNeighbors 47 ↔ 3≤(icosahedralSecants (icosahedralPairLine 47 j)).card) := by decide +kernel

theorem icosahedral_pair_48 : ∀j : Fin 60, (48 : Fin 60)≠j →
    (48 : Fin 60)∈icosahedralSecants (icosahedralPairLine 48 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 48 j) ∧
    (j∈icosahedralNeighbors 48 ↔ 3≤(icosahedralSecants (icosahedralPairLine 48 j)).card) := by decide +kernel

theorem icosahedral_pair_49 : ∀j : Fin 60, (49 : Fin 60)≠j →
    (49 : Fin 60)∈icosahedralSecants (icosahedralPairLine 49 j) ∧
    j∈icosahedralSecants (icosahedralPairLine 49 j) ∧
    (j∈icosahedralNeighbors 49 ↔ 3≤(icosahedralSecants (icosahedralPairLine 49 j)).card) := by decide +kernel


end Holant.Certificates.PlatonicIncidence
