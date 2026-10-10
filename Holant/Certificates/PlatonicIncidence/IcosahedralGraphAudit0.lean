import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock0 (j : Fin 64) : Fin 722 := ⟨0+j.val,by omega⟩

def icosahedralGraphAudit0 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock0 j))

theorem icosahedral_graph_audit_0 : icosahedralGraphAudit0=true := by decide +kernel

theorem icosahedral_graph_entries_0 (t : Fin 722) (hlo : 0≤t.val) (hhi : t.val<64) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_0 j (by simp))
  have he : icosahedralGraphBlock0 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock0,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
