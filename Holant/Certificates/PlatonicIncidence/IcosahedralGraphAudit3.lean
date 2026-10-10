import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock3 (j : Fin 64) : Fin 722 := ⟨192+j.val,by omega⟩

def icosahedralGraphAudit3 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock3 j))

theorem icosahedral_graph_audit_3 : icosahedralGraphAudit3=true := by decide +kernel

theorem icosahedral_graph_entries_3 (t : Fin 722) (hlo : 192≤t.val) (hhi : t.val<256) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-192,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_3 j (by simp))
  have he : icosahedralGraphBlock3 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock3,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
