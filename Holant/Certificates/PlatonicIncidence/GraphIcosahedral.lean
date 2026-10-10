import Holant.Certificates.PlatonicIncidence.GraphIcosahedralRows0
import Holant.Certificates.PlatonicIncidence.GraphIcosahedralRows1
import Holant.Certificates.PlatonicIncidence.GraphIcosahedralRows2
import Holant.Certificates.PlatonicIncidence.GraphIcosahedralRows3
import Holant.Certificates.PlatonicIncidence.GraphIcosahedralRows4
import Holant.Certificates.PlatonicIncidence.GraphIcosahedralRows5
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit0
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit1
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit2
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit3
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit4
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit5
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit6
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit7
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit8
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit9
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit10
import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAudit11

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

theorem icosahedral_neighbor_certificate : (∀i : Fin 60, i∉icosahedralNeighbors i) ∧
    (∀i j : Fin 60, j∈icosahedralNeighbors i ↔ i∈icosahedralNeighbors j) ∧
    (∀i : Fin 60, (icosahedralNeighbors i).card=44) := by decide +kernel

theorem icosahedral_graph_entry (t : Fin 722) : IcosahedralGraphEntry t := by
  by_cases h0 : t.val<64
  · exact icosahedral_graph_entries_0 t (by omega) h0
  by_cases h1 : t.val<128
  · exact icosahedral_graph_entries_1 t (by omega) h1
  by_cases h2 : t.val<192
  · exact icosahedral_graph_entries_2 t (by omega) h2
  by_cases h3 : t.val<256
  · exact icosahedral_graph_entries_3 t (by omega) h3
  by_cases h4 : t.val<320
  · exact icosahedral_graph_entries_4 t (by omega) h4
  by_cases h5 : t.val<384
  · exact icosahedral_graph_entries_5 t (by omega) h5
  by_cases h6 : t.val<448
  · exact icosahedral_graph_entries_6 t (by omega) h6
  by_cases h7 : t.val<512
  · exact icosahedral_graph_entries_7 t (by omega) h7
  by_cases h8 : t.val<576
  · exact icosahedral_graph_entries_8 t (by omega) h8
  by_cases h9 : t.val<640
  · exact icosahedral_graph_entries_9 t (by omega) h9
  by_cases h10 : t.val<704
  · exact icosahedral_graph_entries_10 t (by omega) h10
  exact icosahedral_graph_entries_11 t (by omega) t.isLt

theorem icosahedral_all_pairs : ∀t : Fin 722,∀i∈icosahedralSecants t,∀j∈icosahedralSecants t,
    i=j ∨ icosahedralPairLine i j=t := by
  intro t i hi j hj
  have h := icosahedral_graph_entry t
  rw [←h.1] at hi hj
  have h' := List.all_eq_true.mp h.2 i (by simpa using hi)
  have h'' := List.all_eq_true.mp h' j (by simpa using hj)
  exact of_decide_eq_true h''

end Holant.Certificates.PlatonicIncidence
