import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock9 (j : Fin 64) : Fin 722 := ⟨576+j.val,by omega⟩

def icosahedralAudit9 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock9 j))

theorem icosahedral_audit_9 : icosahedralAudit9=true := by decide +kernel

theorem icosahedral_entries_9 (t : Fin 722) (hlo : 576≤t.val) (hhi : t.val<640) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-576,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_9 j (by simp))
  have he : icosahedralBlock9 j=t := by apply Fin.ext; dsimp [icosahedralBlock9,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
