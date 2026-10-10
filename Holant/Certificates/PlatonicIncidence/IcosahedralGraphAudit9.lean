import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock9 (j : Fin 64) : Fin 722 := ⟨576+j.val,by omega⟩

def icosahedralGraphAudit9 : Bool := (List.finRange 64).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock9 j))

theorem icosahedral_graph_audit_9 : icosahedralGraphAudit9=true := by decide +kernel

theorem icosahedral_graph_entries_9 (t : Fin 722) (hlo : 576≤t.val) (hhi : t.val<640) :
    IcosahedralGraphEntry t := by
  let j : Fin 64 := ⟨t.val-576,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_9 j (by simp))
  have he : icosahedralGraphBlock9 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock9,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
