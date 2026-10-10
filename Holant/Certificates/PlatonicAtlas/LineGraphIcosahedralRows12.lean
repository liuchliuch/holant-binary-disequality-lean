import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows12Block (j : Fin 16) : Fin 272 := ⟨192+j.val,by omega⟩

def icosahedralRows12Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows12Block j))

theorem icosahedralRows12_checked : icosahedralRows12Audit=true := by decide +kernel

theorem icosahedralRows12_entry (i : Fin 272) (hlo : 192 ≤ i.val) (hhi : i.val < 208) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-192,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows12_checked j (by simp))
  have he : icosahedralRows12Block j=i := by apply Fin.ext; dsimp [icosahedralRows12Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
