import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock10 (j : Fin 64) : Fin 722 := ⟨640+j.val,by omega⟩

def icosahedralAudit10 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock10 j))

theorem icosahedral_audit_10 : icosahedralAudit10=true := by decide +kernel

theorem icosahedral_entries_10 (t : Fin 722) (hlo : 640≤t.val) (hhi : t.val<704) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-640,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_10 j (by simp))
  have he : icosahedralBlock10 j=t := by apply Fin.ext; dsimp [icosahedralBlock10,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
