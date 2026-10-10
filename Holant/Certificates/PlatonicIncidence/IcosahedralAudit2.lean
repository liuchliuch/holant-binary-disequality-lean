import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock2 (j : Fin 64) : Fin 722 := ⟨128+j.val,by omega⟩

def icosahedralAudit2 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock2 j))

theorem icosahedral_audit_2 : icosahedralAudit2=true := by decide +kernel

theorem icosahedral_entries_2 (t : Fin 722) (hlo : 128≤t.val) (hhi : t.val<192) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-128,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_2 j (by simp))
  have he : icosahedralBlock2 j=t := by apply Fin.ext; dsimp [icosahedralBlock2,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
