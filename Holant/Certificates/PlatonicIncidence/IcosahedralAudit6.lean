import Holant.Certificates.PlatonicIncidence.IcosahedralAuditData

namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralBlock6 (j : Fin 64) : Fin 722 := ⟨384+j.val,by omega⟩

def icosahedralAudit6 : Bool := (List.finRange 64).all fun j => decide (IcosahedralEntry (icosahedralBlock6 j))

theorem icosahedral_audit_6 : icosahedralAudit6=true := by decide +kernel

theorem icosahedral_entries_6 (t : Fin 722) (hlo : 384≤t.val) (hhi : t.val<448) :
    IcosahedralEntry t := by
  let j : Fin 64 := ⟨t.val-384,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedral_audit_6 j (by simp))
  have he : icosahedralBlock6 j=t := by apply Fin.ext; dsimp [icosahedralBlock6,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicIncidence
