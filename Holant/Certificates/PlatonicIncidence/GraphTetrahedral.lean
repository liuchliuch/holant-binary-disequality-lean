import Holant.Certificates.PlatonicIncidence.GraphData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem tetrahedral_neighbor_certificate : (∀i : Fin 12, i∉tetrahedralNeighbors i) ∧
    (∀i j : Fin 12, j∈tetrahedralNeighbors i ↔ i∈tetrahedralNeighbors j) ∧
    (∀i : Fin 12, (tetrahedralNeighbors i).card=8) := by decide +kernel

theorem tetrahedral_pair_0 : ∀j : Fin 12, (0 : Fin 12)≠j →
    (0 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 0 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 0 j) ∧
    (j∈tetrahedralNeighbors 0 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 0 j)).card) := by decide +kernel

theorem tetrahedral_pair_1 : ∀j : Fin 12, (1 : Fin 12)≠j →
    (1 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 1 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 1 j) ∧
    (j∈tetrahedralNeighbors 1 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 1 j)).card) := by decide +kernel

theorem tetrahedral_pair_2 : ∀j : Fin 12, (2 : Fin 12)≠j →
    (2 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 2 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 2 j) ∧
    (j∈tetrahedralNeighbors 2 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 2 j)).card) := by decide +kernel

theorem tetrahedral_pair_3 : ∀j : Fin 12, (3 : Fin 12)≠j →
    (3 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 3 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 3 j) ∧
    (j∈tetrahedralNeighbors 3 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 3 j)).card) := by decide +kernel

theorem tetrahedral_pair_4 : ∀j : Fin 12, (4 : Fin 12)≠j →
    (4 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 4 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 4 j) ∧
    (j∈tetrahedralNeighbors 4 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 4 j)).card) := by decide +kernel

theorem tetrahedral_pair_5 : ∀j : Fin 12, (5 : Fin 12)≠j →
    (5 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 5 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 5 j) ∧
    (j∈tetrahedralNeighbors 5 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 5 j)).card) := by decide +kernel

theorem tetrahedral_pair_6 : ∀j : Fin 12, (6 : Fin 12)≠j →
    (6 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 6 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 6 j) ∧
    (j∈tetrahedralNeighbors 6 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 6 j)).card) := by decide +kernel

theorem tetrahedral_pair_7 : ∀j : Fin 12, (7 : Fin 12)≠j →
    (7 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 7 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 7 j) ∧
    (j∈tetrahedralNeighbors 7 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 7 j)).card) := by decide +kernel

theorem tetrahedral_pair_8 : ∀j : Fin 12, (8 : Fin 12)≠j →
    (8 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 8 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 8 j) ∧
    (j∈tetrahedralNeighbors 8 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 8 j)).card) := by decide +kernel

theorem tetrahedral_pair_9 : ∀j : Fin 12, (9 : Fin 12)≠j →
    (9 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 9 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 9 j) ∧
    (j∈tetrahedralNeighbors 9 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 9 j)).card) := by decide +kernel

theorem tetrahedral_pair_10 : ∀j : Fin 12, (10 : Fin 12)≠j →
    (10 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 10 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 10 j) ∧
    (j∈tetrahedralNeighbors 10 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 10 j)).card) := by decide +kernel

theorem tetrahedral_pair_11 : ∀j : Fin 12, (11 : Fin 12)≠j →
    (11 : Fin 12)∈tetrahedralSecants (tetrahedralPairLine 11 j) ∧
    j∈tetrahedralSecants (tetrahedralPairLine 11 j) ∧
    (j∈tetrahedralNeighbors 11 ↔ 3≤(tetrahedralSecants (tetrahedralPairLine 11 j)).card) := by decide +kernel

def tetrahedralPairAudit : Bool :=
  (List.finRange 34).all fun t => ((List.finRange 12).filter (fun i => decide (i∈tetrahedralSecants t))).all fun i =>
    ((List.finRange 12).filter (fun i => decide (i∈tetrahedralSecants t))).all fun j => decide (i=j ∨ tetrahedralPairLine i j=t)

theorem tetrahedral_pair_audit : tetrahedralPairAudit=true := by decide +kernel

theorem tetrahedral_all_pairs : ∀t : Fin 34,∀i∈tetrahedralSecants t,∀j∈tetrahedralSecants t,
    i=j ∨ tetrahedralPairLine i j=t := by
  intro t i hi j hj
  have h := List.all_eq_true.mp tetrahedral_pair_audit t (by simp)
  have h' := List.all_eq_true.mp h i (by simpa using hi)
  have h'' := List.all_eq_true.mp h' j (by simpa using hj)
  exact of_decide_eq_true h''

end Holant.Certificates.PlatonicIncidence
