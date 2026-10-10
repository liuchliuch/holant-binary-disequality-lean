import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows15Block (j : Fin 16) : Fin 272 := ⟨240+j.val,by omega⟩

def icosahedralRows15Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows15Block j))

theorem icosahedralRows15_checked : icosahedralRows15Audit=true := by decide +kernel

theorem icosahedralRows15_entry (i : Fin 272) (hlo : 240 ≤ i.val) (hhi : i.val < 256) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-240,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows15_checked j (by simp))
  have he : icosahedralRows15Block j=i := by apply Fin.ext; dsimp [icosahedralRows15Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
