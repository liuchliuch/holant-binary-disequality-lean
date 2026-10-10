import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock11 (j : Fin 18) : Fin 722 := ⟨704+j.val,by omega⟩

def icosahedralAudit11 : Bool := (List.finRange 18).all fun j => decide (IcosahedralEntry (icosahedralBlock11 j))

theorem icosahedral_audit_11 : icosahedralAudit11=true := by decide +kernel

theorem icosahedral_entries_11 (t : Fin 722) (hlo : 704≤t.val) (hhi : t.val<722) :
    IcosahedralEntry t := by
  let j : Fin 18 := ⟨t.val-704,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_11 j (by simp))
  have he : icosahedralBlock11 j=t := by apply Fin.ext; dsimp [icosahedralBlock11,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
