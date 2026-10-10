import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock0 (j : Fin 64) : Fin 722 := ⟨0+j.val,by omega⟩

def icosahedralAudit0 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock0 j))

theorem icosahedral_audit_0 : icosahedralAudit0=true := by decide +kernel

theorem icosahedral_entries_0 (t : Fin 722) (hlo : 0≤t.val) (hhi : t.val<64) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-0,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_0 j (by simp))
  have he : icosahedralBlock0 j=t := by apply Fin.ext; dsimp [icosahedralBlock0,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
