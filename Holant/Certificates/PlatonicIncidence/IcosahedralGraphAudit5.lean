import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock5 (j : Fin 64) : Fin 722 := ⟨320+j.val,by omega⟩

def icosahedralGraphAudit5 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock5 j))

theorem icosahedral_graph_audit_5 : icosahedralGraphAudit5=true := by decide +kernel

theorem icosahedral_graph_entries_5 (t : Fin 722) (hlo : 320≤t.val) (hhi : t.val<384) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-320,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_5 j (by simp))
  have he : icosahedralGraphBlock5 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock5,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
