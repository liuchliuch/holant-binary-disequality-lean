import Holant.Certificates.PlatonicIncidence.IcosahedralGraphAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralGraphBlock11 (j : Fin 18) : Fin 722 := ⟨704+j.val,by omega⟩

def icosahedralGraphAudit11 : Bool := (List.finRange 18).all fun j => decide (IcosahedralGraphEntry (icosahedralGraphBlock11 j))

theorem icosahedral_graph_audit_11 : icosahedralGraphAudit11=true := by decide +kernel

theorem icosahedral_graph_entries_11 (t : Fin 722) (hlo : 704≤t.val) (hhi : t.val<722) :
    IcosahedralGraphEntry t := by
  let j : Fin 18 := ⟨t.val-704,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_graph_audit_11 j (by simp))
  have he : icosahedralGraphBlock11 j=t := by apply Fin.ext; dsimp [icosahedralGraphBlock11,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
