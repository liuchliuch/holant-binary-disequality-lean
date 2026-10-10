import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows3Block (j : Fin 16) : Fin 272 := ⟨48+j.val,by omega⟩

def icosahedralRows3Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows3Block j))

theorem icosahedralRows3_checked : icosahedralRows3Audit=true := by decide +kernel

theorem icosahedralRows3_entry (i : Fin 272) (hlo : 48 ≤ i.val) (hhi : i.val < 64) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-48,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows3_checked j (by simp))
  have he : icosahedralRows3Block j=i := by apply Fin.ext; dsimp [icosahedralRows3Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
