import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows16Block (j : Fin 16) : Fin 272 := ⟨256+j.val,by omega⟩

def icosahedralRows16Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows16Block j))

theorem icosahedralRows16_checked : icosahedralRows16Audit=true := by decide +kernel

theorem icosahedralRows16_entry (i : Fin 272) (hlo : 256 ≤ i.val) (hhi : i.val < 272) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-256,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows16_checked j (by simp))
  have he : icosahedralRows16Block j=i := by apply Fin.ext; dsimp [icosahedralRows16Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
