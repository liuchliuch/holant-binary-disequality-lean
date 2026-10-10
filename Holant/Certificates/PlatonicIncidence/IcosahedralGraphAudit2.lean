import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock2 (j : Fin 64) : Fin 722 := ⟨128+j.val,by omega⟩

def icosahedralGraphAudit2 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock2 j))

theorem icosahedral_graph_audit_2 : icosahedralGraphAudit2=true := by decide +kernel

theorem icosahedral_graph_entries_2 (t : Fin 722) (hlo : 128≤t.val) (hhi : t.val<192) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-128,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_2 j (by simp))
  have he : icosahedralGraphBlock2 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock2,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
