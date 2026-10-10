import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock4 (j : Fin 64) : Fin 722 := ⟨256+j.val,by omega⟩

def icosahedralGraphAudit4 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock4 j))

theorem icosahedral_graph_audit_4 : icosahedralGraphAudit4=true := by decide +kernel

theorem icosahedral_graph_entries_4 (t : Fin 722) (hlo : 256≤t.val) (hhi : t.val<320) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-256,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_4 j (by simp))
  have he : icosahedralGraphBlock4 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock4,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
