import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock1 (j : Fin 64) : Fin 722 := ⟨64+j.val,by omega⟩

def icosahedralGraphAudit1 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock1 j))

theorem icosahedral_graph_audit_1 : icosahedralGraphAudit1=true := by decide +kernel

theorem icosahedral_graph_entries_1 (t : Fin 722) (hlo : 64≤t.val) (hhi : t.val<128) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-64,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_1 j (by simp))
  have he : icosahedralGraphBlock1 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock1,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
