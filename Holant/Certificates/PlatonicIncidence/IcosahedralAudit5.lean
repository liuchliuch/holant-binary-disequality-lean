import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock5 (j : Fin 64) : Fin 722 := ⟨320+j.val,by omega⟩

def icosahedralAudit5 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock5 j))

theorem icosahedral_audit_5 : icosahedralAudit5=true := by decide +kernel

theorem icosahedral_entries_5 (t : Fin 722) (hlo : 320≤t.val) (hhi : t.val<384) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-320,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_5 j (by simp))
  have he : icosahedralBlock5 j=t := by apply Fin.ext; dsimp [icosahedralBlock5,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
