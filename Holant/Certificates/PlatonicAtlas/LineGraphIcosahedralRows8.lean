import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows8Block (j : Fin 16) : Fin 272 := ⟨128+j.val,by omega⟩

def icosahedralRows8Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows8Block j))

theorem icosahedralRows8_checked : icosahedralRows8Audit=true := by decide +kernel

theorem icosahedralRows8_entry (i : Fin 272) (hlo : 128 ≤ i.val) (hhi : i.val < 144) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-128,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows8_checked j (by simp))
  have he : icosahedralRows8Block j=i := by apply Fin.ext; dsimp [icosahedralRows8Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
