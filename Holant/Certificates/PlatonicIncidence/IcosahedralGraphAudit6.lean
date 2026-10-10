import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock6 (j : Fin 64) : Fin 722 := ⟨384+j.val,by omega⟩

def icosahedralGraphAudit6 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock6 j))

theorem icosahedral_graph_audit_6 : icosahedralGraphAudit6=true := by decide +kernel

theorem icosahedral_graph_entries_6 (t : Fin 722) (hlo : 384≤t.val) (hhi : t.val<448) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-384,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_6 j (by simp))
  have he : icosahedralGraphBlock6 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock6,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
