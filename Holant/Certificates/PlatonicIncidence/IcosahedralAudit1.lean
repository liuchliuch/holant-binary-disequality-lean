import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock1 (j : Fin 64) : Fin 722 := ⟨64+j.val,by omega⟩

def icosahedralAudit1 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock1 j))

theorem icosahedral_audit_1 : icosahedralAudit1=true := by decide +kernel

theorem icosahedral_entries_1 (t : Fin 722) (hlo : 64≤t.val) (hhi : t.val<128) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-64,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_1 j (by simp))
  have he : icosahedralBlock1 j=t := by apply Fin.ext; dsimp [icosahedralBlock1,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
