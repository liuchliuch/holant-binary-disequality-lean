import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows4Block (j : Fin 16) : Fin 272 := ⟨64+j.val,by omega⟩

def icosahedralRows4Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows4Block j))

theorem icosahedralRows4_checked : icosahedralRows4Audit=true := by decide +kernel

theorem icosahedralRows4_entry (i : Fin 272) (hlo : 64 ≤ i.val) (hhi : i.val < 80) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-64,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows4_checked j (by simp))
  have he : icosahedralRows4Block j=i := by apply Fin.ext; dsimp [icosahedralRows4Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
