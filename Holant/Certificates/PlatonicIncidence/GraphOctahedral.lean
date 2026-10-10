import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem octahedral_neighbor_certificate : (∀i : Fin 24, i∉octahedralNeighbors i) ∧
    (∀i j : Fin 24, j∈octahedralNeighbors i ↔ i∈octahedralNeighbors j) ∧
    (∀i : Fin 24, (octahedralNeighbors i).card=17) := by decide +kernel

theorem octahedral_pair_0 : ∀j : Fin 24, (0 : Fin 24)≠j →
    (0 : Fin 24)∈octahedralSecants (octahedralPairLine 0 j) ∧
    j∈octahedralSecants (octahedralPairLine 0 j) ∧
    (j∈octahedralNeighbors 0 ↔ 3≤(octahedralSecants (octahedralPairLine 0 j)).card) := by decide +kernel

theorem octahedral_pair_1 : ∀j : Fin 24, (1 : Fin 24)≠j →
    (1 : Fin 24)∈octahedralSecants (octahedralPairLine 1 j) ∧
    j∈octahedralSecants (octahedralPairLine 1 j) ∧
    (j∈octahedralNeighbors 1 ↔ 3≤(octahedralSecants (octahedralPairLine 1 j)).card) := by decide +kernel

theorem octahedral_pair_2 : ∀j : Fin 24, (2 : Fin 24)≠j →
    (2 : Fin 24)∈octahedralSecants (octahedralPairLine 2 j) ∧
    j∈octahedralSecants (octahedralPairLine 2 j) ∧
    (j∈octahedralNeighbors 2 ↔ 3≤(octahedralSecants (octahedralPairLine 2 j)).card) := by decide +kernel

theorem octahedral_pair_3 : ∀j : Fin 24, (3 : Fin 24)≠j →
    (3 : Fin 24)∈octahedralSecants (octahedralPairLine 3 j) ∧
    j∈octahedralSecants (octahedralPairLine 3 j) ∧
    (j∈octahedralNeighbors 3 ↔ 3≤(octahedralSecants (octahedralPairLine 3 j)).card) := by decide +kernel

theorem octahedral_pair_4 : ∀j : Fin 24, (4 : Fin 24)≠j →
    (4 : Fin 24)∈octahedralSecants (octahedralPairLine 4 j) ∧
    j∈octahedralSecants (octahedralPairLine 4 j) ∧
    (j∈octahedralNeighbors 4 ↔ 3≤(octahedralSecants (octahedralPairLine 4 j)).card) := by decide +kernel

theorem octahedral_pair_5 : ∀j : Fin 24, (5 : Fin 24)≠j →
    (5 : Fin 24)∈octahedralSecants (octahedralPairLine 5 j) ∧
    j∈octahedralSecants (octahedralPairLine 5 j) ∧
    (j∈octahedralNeighbors 5 ↔ 3≤(octahedralSecants (octahedralPairLine 5 j)).card) := by decide +kernel

theorem octahedral_pair_6 : ∀j : Fin 24, (6 : Fin 24)≠j →
    (6 : Fin 24)∈octahedralSecants (octahedralPairLine 6 j) ∧
    j∈octahedralSecants (octahedralPairLine 6 j) ∧
    (j∈octahedralNeighbors 6 ↔ 3≤(octahedralSecants (octahedralPairLine 6 j)).card) := by decide +kernel

theorem octahedral_pair_7 : ∀j : Fin 24, (7 : Fin 24)≠j →
    (7 : Fin 24)∈octahedralSecants (octahedralPairLine 7 j) ∧
    j∈octahedralSecants (octahedralPairLine 7 j) ∧
    (j∈octahedralNeighbors 7 ↔ 3≤(octahedralSecants (octahedralPairLine 7 j)).card) := by decide +kernel

theorem octahedral_pair_8 : ∀j : Fin 24, (8 : Fin 24)≠j →
    (8 : Fin 24)∈octahedralSecants (octahedralPairLine 8 j) ∧
    j∈octahedralSecants (octahedralPairLine 8 j) ∧
    (j∈octahedralNeighbors 8 ↔ 3≤(octahedralSecants (octahedralPairLine 8 j)).card) := by decide +kernel

theorem octahedral_pair_9 : ∀j : Fin 24, (9 : Fin 24)≠j →
    (9 : Fin 24)∈octahedralSecants (octahedralPairLine 9 j) ∧
    j∈octahedralSecants (octahedralPairLine 9 j) ∧
    (j∈octahedralNeighbors 9 ↔ 3≤(octahedralSecants (octahedralPairLine 9 j)).card) := by decide +kernel

theorem octahedral_pair_10 : ∀j : Fin 24, (10 : Fin 24)≠j →
    (10 : Fin 24)∈octahedralSecants (octahedralPairLine 10 j) ∧
    j∈octahedralSecants (octahedralPairLine 10 j) ∧
    (j∈octahedralNeighbors 10 ↔ 3≤(octahedralSecants (octahedralPairLine 10 j)).card) := by decide +kernel

theorem octahedral_pair_11 : ∀j : Fin 24, (11 : Fin 24)≠j →
    (11 : Fin 24)∈octahedralSecants (octahedralPairLine 11 j) ∧
    j∈octahedralSecants (octahedralPairLine 11 j) ∧
    (j∈octahedralNeighbors 11 ↔ 3≤(octahedralSecants (octahedralPairLine 11 j)).card) := by decide +kernel

theorem octahedral_pair_12 : ∀j : Fin 24, (12 : Fin 24)≠j →
    (12 : Fin 24)∈octahedralSecants (octahedralPairLine 12 j) ∧
    j∈octahedralSecants (octahedralPairLine 12 j) ∧
    (j∈octahedralNeighbors 12 ↔ 3≤(octahedralSecants (octahedralPairLine 12 j)).card) := by decide +kernel

theorem octahedral_pair_13 : ∀j : Fin 24, (13 : Fin 24)≠j →
    (13 : Fin 24)∈octahedralSecants (octahedralPairLine 13 j) ∧
    j∈octahedralSecants (octahedralPairLine 13 j) ∧
    (j∈octahedralNeighbors 13 ↔ 3≤(octahedralSecants (octahedralPairLine 13 j)).card) := by decide +kernel

theorem octahedral_pair_14 : ∀j : Fin 24, (14 : Fin 24)≠j →
    (14 : Fin 24)∈octahedralSecants (octahedralPairLine 14 j) ∧
    j∈octahedralSecants (octahedralPairLine 14 j) ∧
    (j∈octahedralNeighbors 14 ↔ 3≤(octahedralSecants (octahedralPairLine 14 j)).card) := by decide +kernel

theorem octahedral_pair_15 : ∀j : Fin 24, (15 : Fin 24)≠j →
    (15 : Fin 24)∈octahedralSecants (octahedralPairLine 15 j) ∧
    j∈octahedralSecants (octahedralPairLine 15 j) ∧
    (j∈octahedralNeighbors 15 ↔ 3≤(octahedralSecants (octahedralPairLine 15 j)).card) := by decide +kernel

theorem octahedral_pair_16 : ∀j : Fin 24, (16 : Fin 24)≠j →
    (16 : Fin 24)∈octahedralSecants (octahedralPairLine 16 j) ∧
    j∈octahedralSecants (octahedralPairLine 16 j) ∧
    (j∈octahedralNeighbors 16 ↔ 3≤(octahedralSecants (octahedralPairLine 16 j)).card) := by decide +kernel

theorem octahedral_pair_17 : ∀j : Fin 24, (17 : Fin 24)≠j →
    (17 : Fin 24)∈octahedralSecants (octahedralPairLine 17 j) ∧
    j∈octahedralSecants (octahedralPairLine 17 j) ∧
    (j∈octahedralNeighbors 17 ↔ 3≤(octahedralSecants (octahedralPairLine 17 j)).card) := by decide +kernel

theorem octahedral_pair_18 : ∀j : Fin 24, (18 : Fin 24)≠j →
    (18 : Fin 24)∈octahedralSecants (octahedralPairLine 18 j) ∧
    j∈octahedralSecants (octahedralPairLine 18 j) ∧
    (j∈octahedralNeighbors 18 ↔ 3≤(octahedralSecants (octahedralPairLine 18 j)).card) := by decide +kernel

theorem octahedral_pair_19 : ∀j : Fin 24, (19 : Fin 24)≠j →
    (19 : Fin 24)∈octahedralSecants (octahedralPairLine 19 j) ∧
    j∈octahedralSecants (octahedralPairLine 19 j) ∧
    (j∈octahedralNeighbors 19 ↔ 3≤(octahedralSecants (octahedralPairLine 19 j)).card) := by decide +kernel

theorem octahedral_pair_20 : ∀j : Fin 24, (20 : Fin 24)≠j →
    (20 : Fin 24)∈octahedralSecants (octahedralPairLine 20 j) ∧
    j∈octahedralSecants (octahedralPairLine 20 j) ∧
    (j∈octahedralNeighbors 20 ↔ 3≤(octahedralSecants (octahedralPairLine 20 j)).card) := by decide +kernel

theorem octahedral_pair_21 : ∀j : Fin 24, (21 : Fin 24)≠j →
    (21 : Fin 24)∈octahedralSecants (octahedralPairLine 21 j) ∧
    j∈octahedralSecants (octahedralPairLine 21 j) ∧
    (j∈octahedralNeighbors 21 ↔ 3≤(octahedralSecants (octahedralPairLine 21 j)).card) := by decide +kernel

theorem octahedral_pair_22 : ∀j : Fin 24, (22 : Fin 24)≠j →
    (22 : Fin 24)∈octahedralSecants (octahedralPairLine 22 j) ∧
    j∈octahedralSecants (octahedralPairLine 22 j) ∧
    (j∈octahedralNeighbors 22 ↔ 3≤(octahedralSecants (octahedralPairLine 22 j)).card) := by decide +kernel

theorem octahedral_pair_23 : ∀j : Fin 24, (23 : Fin 24)≠j →
    (23 : Fin 24)∈octahedralSecants (octahedralPairLine 23 j) ∧
    j∈octahedralSecants (octahedralPairLine 23 j) ∧
    (j∈octahedralNeighbors 23 ↔ 3≤(octahedralSecants (octahedralPairLine 23 j)).card) := by decide +kernel

def octahedralPairAudit : Bool :=
  (List.finRange 122).all fun t => ((List.finRange 24).filter (fun i => decide (i∈octahedralSecants t))).all fun i =>
    ((List.finRange 24).filter (fun i => decide (i∈octahedralSecants t))).all fun j => decide (i=j ∨ octahedralPairLine i j=t)

theorem octahedral_pair_audit : octahedralPairAudit=true := by decide +kernel

theorem octahedral_all_pairs : ∀t : Fin 122,∀i∈octahedralSecants t,∀j∈octahedralSecants t,
    i=j ∨ octahedralPairLine i j=t := by
  intro t i hi j hj
  have h := List.all_eq_true.mp octahedral_pair_audit t (by simp)
  have h' := List.all_eq_true.mp h i (by simpa using hi)
  have h'' := List.all_eq_true.mp h' j (by simpa using hj)
  exact of_decide_eq_true h''

end Holant.Certificates.PlatonicIncidence
