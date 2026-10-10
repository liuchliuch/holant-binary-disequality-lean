import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows2Block (j : Fin 16) : Fin 272 := ⟨32+j.val,by omega⟩

def icosahedralRows2Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows2Block j))

theorem icosahedralRows2_checked : icosahedralRows2Audit=true := by decide +kernel

theorem icosahedralRows2_entry (i : Fin 272) (hlo : 32 ≤ i.val) (hhi : i.val < 48) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-32,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows2_checked j (by simp))
  have he : icosahedralRows2Block j=i := by apply Fin.ext; dsimp [icosahedralRows2Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
