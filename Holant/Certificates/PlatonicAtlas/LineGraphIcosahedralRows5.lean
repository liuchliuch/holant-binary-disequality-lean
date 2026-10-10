import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows5Block (j : Fin 16) : Fin 272 := ⟨80+j.val,by omega⟩

def icosahedralRows5Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows5Block j))

theorem icosahedralRows5_checked : icosahedralRows5Audit=true := by decide +kernel

theorem icosahedralRows5_entry (i : Fin 272) (hlo : 80 ≤ i.val) (hhi : i.val < 96) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-80,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows5_checked j (by simp))
  have he : icosahedralRows5Block j=i := by apply Fin.ext; dsimp [icosahedralRows5Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
