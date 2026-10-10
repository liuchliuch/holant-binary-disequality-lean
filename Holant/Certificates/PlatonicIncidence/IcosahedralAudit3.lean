import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock3 (j : Fin 64) : Fin 722 := ⟨192+j.val,by omega⟩

def icosahedralAudit3 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock3 j))

theorem icosahedral_audit_3 : icosahedralAudit3=true := by decide +kernel

theorem icosahedral_entries_3 (t : Fin 722) (hlo : 192≤t.val) (hhi : t.val<256) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-192,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_3 j (by simp))
  have he : icosahedralBlock3 j=t := by apply Fin.ext; dsimp [icosahedralBlock3,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
