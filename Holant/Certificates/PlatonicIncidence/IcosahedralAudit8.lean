import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock8 (j : Fin 64) : Fin 722 := ⟨512+j.val,by omega⟩

def icosahedralAudit8 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock8 j))

theorem icosahedral_audit_8 : icosahedralAudit8=true := by decide +kernel

theorem icosahedral_entries_8 (t : Fin 722) (hlo : 512≤t.val) (hhi : t.val<576) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-512,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_8 j (by simp))
  have he : icosahedralBlock8 j=t := by apply Fin.ext; dsimp [icosahedralBlock8,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
