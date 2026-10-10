import Holant.Certificates.PlatonicAtlas.LineGraphData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option backward.isDefEq.respectTransparency false

def icosahedralRows6Block (j : Fin 16) : Fin 272 := ⟨96+j.val,by omega⟩

def icosahedralRows6Audit : Bool := (List.finRange 16).all fun j => decide (RichEntry .icosahedral (icosahedralRows6Block j))

theorem icosahedralRows6_checked : icosahedralRows6Audit=true := by decide +kernel

theorem icosahedralRows6_entry (i : Fin 272) (hlo : 96 ≤ i.val) (hhi : i.val < 112) : RichEntry .icosahedral i := by
  let j : Fin 16 := ⟨i.val-96,by omega⟩
  have h := of_decide_eq_true (List.all_eq_true.mp icosahedralRows6_checked j (by simp))
  have he : icosahedralRows6Block j=i := by apply Fin.ext; dsimp [icosahedralRows6Block,j]; omega
  rwa [he] at h

end Holant.Certificates.PlatonicAtlas
