import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock7 (j : Fin 64) : Fin 722 := ⟨448+j.val,by omega⟩

def icosahedralGraphAudit7 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock7 j))

theorem icosahedral_graph_audit_7 : icosahedralGraphAudit7=true := by decide +kernel

theorem icosahedral_graph_entries_7 (t : Fin 722) (hlo : 448≤t.val) (hhi : t.val<512) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-448,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_7 j (by simp))
  have he : icosahedralGraphBlock7 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock7,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
