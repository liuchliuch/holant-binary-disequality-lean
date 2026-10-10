import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows9Block (j : Fin 16) : Fin 272 := ⟨144+j.val,by omega⟩

def icosahedralRows9Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows9Block j))

theorem icosahedralRows9_checked : icosahedralRows9Audit=true := by decide +kernel

theorem icosahedralRows9_entry (i : Fin 272) (hlo : 144 ≤ i.val) (hhi : i.val < 160) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-144,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows9_checked j (by simp))
  have he : icosahedralRows9Block j=i := by apply Fin.ext; dsimp [icosahedralRows9Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
