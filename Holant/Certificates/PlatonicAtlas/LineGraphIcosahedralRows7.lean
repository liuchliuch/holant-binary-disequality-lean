import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows7Block (j : Fin 16) : Fin 272 := ⟨112+j.val,by omega⟩

def icosahedralRows7Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows7Block j))

theorem icosahedralRows7_checked : icosahedralRows7Audit=true := by decide +kernel

theorem icosahedralRows7_entry (i : Fin 272) (hlo : 112 ≤ i.val) (hhi : i.val < 128) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-112,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows7_checked j (by simp))
  have he : icosahedralRows7Block j=i := by apply Fin.ext; dsimp [icosahedralRows7Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
